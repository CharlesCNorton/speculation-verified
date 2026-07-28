(******************************************************************************)
(*                                                                            *)
(*                 Optimistic Parallel Transaction Execution                  *)
(*                                                                            *)
(*     Optimistic concurrency control over a linearly ordered block of        *)
(*     transactions: speculative runs against arbitrary read sources,         *)
(*     ordered commit-time validation by storage, balance, and nonce read     *)
(*     logs, re-execution on conflict.  Contract-scoped storage, calls with   *)
(*     arguments, return values, attached value, and per-frame reverts, an    *)
(*     in-flight bank with point-of-pay settlement, nonce-gated admission,    *)
(*     state-dependent gas with cold/warm access, intrinsic cost, a base      *)
(*     fee with burn, and transition refunds.  Machine-checked safety,        *)
(*     scheduler optimality, retry convergence and total work, conflict       *)
(*     freedom with an executable footprint checker, parallel depth with a    *)
(*     constructed critical path, an operational concurrent scheduler with    *)
(*     versioned validation, incarnations, fairness, and liveness, an AVL     *)
(*     engine with persistence, and gas, transfer, nonce, and supply          *)
(*     ledgers.                                                               *)
(*                                                                            *)
(*     References: Kung HT, Robinson JT. On optimistic methods for            *)
(*     concurrency control. ACM TODS. 1981;6(2):213-226.  Gelashvili R,       *)
(*     et al. Block-STM. PPoPP 2023.                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: July 27, 2026                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List Arith Bool Lia Permutation NArith Wf_nat.
Import ListNotations.

(** ** Storage keys, bank, nonces

    Storage is scoped by executing contract: a key is a contract paired with
    a slot.  The bank and the nonce map are keyed by account. *)

Definition addr : Type := nat.
Definition val : Type := nat.
Definition key : Type := (addr * addr)%type.

Definition keqb (k1 k2 : key) : bool :=
  Nat.eqb (fst k1) (fst k2) && Nat.eqb (snd k1) (snd k2).

Lemma keqb_eq : forall k1 k2, keqb k1 k2 = true <-> k1 = k2.
Proof.
  intros [a1 b1] [a2 b2]. unfold keqb. simpl.
  rewrite andb_true_iff, !Nat.eqb_eq. split.
  - intros [-> ->]. reflexivity.
  - intros H. injection H as -> ->. split; reflexivity.
Qed.

Lemma keqb_refl : forall k, keqb k k = true.
Proof. intros k. apply keqb_eq. reflexivity. Qed.

Lemma keqb_neq : forall k1 k2, keqb k1 k2 = false <-> k1 <> k2.
Proof.
  intros k1 k2. split.
  - intros H E. rewrite E, keqb_refl in H. discriminate.
  - intros H. destruct (keqb k1 k2) eqn:E; [| reflexivity].
    apply keqb_eq in E. congruence.
Qed.

Definition storage : Type := key -> val.
Definition bank : Type := addr -> nat.
Notation nonces := bank (only parsing).

Definition kupd (s : storage) (k : key) (v : val) : storage :=
  fun k' => if keqb k' k then v else s k'.

Definition bupd (b : bank) (a : addr) (n : nat) : bank :=
  fun a' => if Nat.eqb a' a then n else b a'.

Lemma kupd_same : forall s k v, kupd s k v k = v.
Proof. intros. unfold kupd. rewrite keqb_refl. reflexivity. Qed.

Lemma kupd_other : forall s k v k', k' <> k -> kupd s k v k' = s k'.
Proof.
  intros s k v k' H. unfold kupd.
  destruct (keqb k' k) eqn:E; [apply keqb_eq in E; congruence | reflexivity].
Qed.

Lemma bupd_same : forall b a n, bupd b a n a = n.
Proof. intros. unfold bupd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma bupd_other : forall b a n a', a' <> a -> bupd b a n a' = b a'.
Proof.
  intros b a n a' H. unfold bupd.
  apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

(** ** Access sets *)

Definition inkey (k : key) (l : list key) : bool := existsb (keqb k) l.
Definition inaddr (a : addr) (l : list addr) : bool := existsb (Nat.eqb a) l.

(** ** Write buffer *)

Definition buffer : Type := list (key * val).

Fixpoint wlookup (w : buffer) (k : key) : option val :=
  match w with
  | [] => None
  | (k', v) :: rest => if keqb k k' then Some v else wlookup rest k
  end.

Definition commit (s : storage) (w : buffer) : storage :=
  fold_right (fun p s' => kupd s' (fst p) (snd p)) s w.

Lemma commit_untouched :
  forall w s k, ~ In k (map fst w) -> commit s w k = s k.
Proof.
  induction w as [| [k0 v0] w' IH]; simpl; intros s k Hnin.
  - reflexivity.
  - unfold kupd. destruct (keqb k k0) eqn:He.
    + apply keqb_eq in He. subst. exfalso. apply Hnin. left. reflexivity.
    + apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

Lemma commit_wlookup :
  forall w s k v, wlookup w k = Some v -> commit s w k = v.
Proof.
  induction w as [| [k0 v0] w' IH]; simpl; intros s k v Hlk.
  - discriminate.
  - unfold kupd. destruct (keqb k k0) eqn:He.
    + injection Hlk as <-. reflexivity.
    + apply IH. exact Hlk.
Qed.

(** ** Transfers

    A transfer carries its sender: calls and payments make contracts pay
    from their own accounts.  Settlement applies transfers in program
    order; [apply_ok] certifies stepwise sufficiency, under which
    [apply_law] is the exact per-account ledger. *)

Definition transfer : Type := (addr * addr * nat)%type.

Fixpoint apply_tvs (b : bank) (l : list transfer) : bank :=
  match l with
  | [] => b
  | (s, d, amt) :: r =>
      apply_tvs (bupd (bupd b s (b s - amt)) d
                      (bupd b s (b s - amt) d + amt)) r
  end.

Fixpoint apply_ok (b : bank) (l : list transfer) : bool :=
  match l with
  | [] => true
  | (s, d, amt) :: r =>
      (amt <=? b s) &&
      apply_ok (bupd (bupd b s (b s - amt)) d
                     (bupd b s (b s - amt) d + amt)) r
  end.

Fixpoint outsum (f : addr) (l : list transfer) : nat :=
  match l with
  | [] => 0
  | (s, _, amt) :: r => (if Nat.eqb s f then amt else 0) + outsum f r
  end.

Fixpoint insum (f : addr) (l : list transfer) : nat :=
  match l with
  | [] => 0
  | (_, d, amt) :: r => (if Nat.eqb d f then amt else 0) + insum f r
  end.

Lemma apply_law :
  forall l b,
    apply_ok b l = true ->
    forall f, apply_tvs b l f + outsum f l = b f + insum f l.
Proof.
  induction l as [| [[s d] amt] r IH]; simpl; intros b Hok f.
  - lia.
  - apply andb_true_iff in Hok. destruct Hok as [Hle Hok].
    apply Nat.leb_le in Hle.
    set (b1 := bupd b s (b s - amt)).
    set (b2 := bupd b1 d (b1 d + amt)).
    specialize (IH b2 Hok f).
    destruct (Nat.eqb s f) eqn:Hsf; destruct (Nat.eqb d f) eqn:Hdf.
    + apply Nat.eqb_eq in Hsf. apply Nat.eqb_eq in Hdf. subst s d.
      assert (Hb2 : b2 f = b f).
      { unfold b2. rewrite bupd_same. unfold b1. rewrite bupd_same. lia. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_eq in Hsf. apply Nat.eqb_neq in Hdf. subst s.
      assert (Hb2 : b2 f = b f - amt).
      { unfold b2. rewrite (bupd_other b1 d (b1 d + amt) f) by congruence.
        unfold b1. rewrite bupd_same. reflexivity. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_neq in Hsf. apply Nat.eqb_eq in Hdf. subst d.
      assert (Hb2 : b2 f = b f + amt).
      { unfold b2. rewrite bupd_same. unfold b1.
        rewrite (bupd_other b s (b s - amt) f) by congruence. reflexivity. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_neq in Hsf. apply Nat.eqb_neq in Hdf.
      assert (Hb2 : b2 f = b f).
      { unfold b2. rewrite (bupd_other b1 d (b1 d + amt) f) by congruence.
        unfold b1. rewrite (bupd_other b s (b s - amt) f) by congruence.
        reflexivity. }
      rewrite Hb2 in IH. lia.
Qed.

Lemma apply_app :
  forall l1 l2 b, apply_tvs b (l1 ++ l2) = apply_tvs (apply_tvs b l1) l2.
Proof.
  induction l1 as [| [[s d] amt] r IH]; simpl; intros l2 b.
  - reflexivity.
  - apply IH.
Qed.

Lemma apply_ok_app :
  forall l1 l2 b,
    apply_ok b (l1 ++ l2)
    = apply_ok b l1 && apply_ok (apply_tvs b l1) l2.
Proof.
  induction l1 as [| [[s d] amt] r IH]; simpl; intros l2 b.
  - reflexivity.
  - destruct (amt <=? b s); simpl; [apply IH | reflexivity].
Qed.

(** ** Transactions

    [TRet] ends a frame successfully with a return value; [TDone] returns
    zero.  [TBal] reads an account's in-flight balance: the prefix-bank
    answer adjusted by the transaction's own upfront gas hold, settled
    payments, and receipts.  [TPay] settles at the point of pay against the
    in-flight bank and passes the outcome to its continuation.  [TNonce]
    reads the prefix nonce map.  [TWhile] loops on a storage slot under an
    arbitrary decidable test.  [TCall] runs another contract's code on an
    argument in its own storage scope and frame, optionally transferring
    value settled in-flight at the call; the continuation receives the
    callee's return value, or [None] on revert or on an unfunded value
    transfer.  A reverted frame keeps its read logs and gas consumption and
    surrenders its writes, events, transfers, refunds, bank deltas, and
    storage warmth; account warmth charged at the call site survives. *)

Inductive tx : Type :=
| TDone   : tx
| TRet    : val -> tx
| TRevert : tx
| TWrite  : addr -> val -> tx -> tx
| TRead   : addr -> (val -> tx) -> tx
| TBal    : addr -> (nat -> tx) -> tx
| TNonce  : addr -> (nat -> tx) -> tx
| TWhile  : addr -> (val -> bool) -> tx -> tx -> tx
| TEmit   : val -> tx -> tx
| TPay    : addr -> nat -> (bool -> tx) -> tx
| TCall   : addr -> val -> nat -> (option val -> tx) -> tx.

Fixpoint tseq (t1 t2 : tx) : tx :=
  match t1 with
  | TDone => t2
  | TRet v => TRet v
  | TRevert => TRevert
  | TWrite a v k => TWrite a v (tseq k t2)
  | TRead a k => TRead a (fun v => tseq (k v) t2)
  | TBal a k => TBal a (fun v => tseq (k v) t2)
  | TNonce a k => TNonce a (fun v => tseq (k v) t2)
  | TWhile a tst b k => TWhile a tst b (tseq k t2)
  | TEmit e k => TEmit e (tseq k t2)
  | TPay d amt k => TPay d amt (fun ok => tseq (k ok) t2)
  | TCall c arg amt k => TCall c arg amt (fun r => tseq (k r) t2)
  end.

Fixpoint trepeat (n : nat) (body : tx) : tx :=
  match n with
  | 0 => TDone
  | S m => tseq body (trepeat m body)
  end.

(** A block item: fee account (transaction sender, top-level executing
    account, and nonce owner), the expected nonce, the transaction, its gas
    limit, and its tip per gas above the base fee. *)

Definition item : Type := (addr * nat * tx * nat * nat)%type.

(** ** Read sources

    A speculation answers the n-th fall-through storage read, the n-th
    balance read, and the n-th nonce read, with no consistency required
    between or within them. *)

Definition reader : Type := nat -> key -> val.
Definition breader : Type := nat -> addr -> nat.
Definition nreader : Type := nat -> addr -> nat.

Definition of_state (s : storage) : reader := fun _ k => s k.
Definition of_bank (b : bank) : breader := fun _ a => b a.
Definition of_nonces (nm : nonces) : nreader := fun _ a => nm a.

(** ** Gas costs

    Storage writes price by transition: setting a zero slot to a nonzero
    value costs [c_sset], every other write [c_sreset].  First touches of a
    storage key in a transaction add the cold surcharge [c_cold], first
    touches of an account [c_acold]; the fee account and the coinbase start
    warm.  [c_base] is the intrinsic cost charged to every admitted
    transaction before its first operation. *)

Record costs : Type := Costs {
  c_sset : nat; c_sreset : nat; c_read : nat; c_bal : nat; c_nonce : nat;
  c_while : nat; c_emit : nat; c_pay : nat; c_call : nat;
  c_cold : nat; c_acold : nat; c_base : nat
}.

(** ** Outcomes

    An outcome carries the three read logs, the write overlay, events and
    settled transfers in program order, the completion flag, the frame's
    return value, remaining gas, accrued refund, the in-flight bank deltas,
    the next read ordinals, and the warm storage-key and account sets.  The
    record representation lets every projection of a composed outcome
    reduce definitionally. *)

Record out : Type := Out {
  o_slog : list (key * val);
  o_blog : list (addr * nat);
  o_nlog : list (addr * nat);
  o_buf  : buffer;
  o_evs  : list val;
  o_tvs  : list transfer;
  o_ok   : bool;
  o_ret  : val;
  o_gas  : nat;
  o_ref  : nat;
  o_cred : addr -> nat;
  o_deb  : addr -> nat;
  o_n    : nat;
  o_bn   : nat;
  o_nn   : nat;
  o_acc  : list key;
  o_aacc : list addr
}.

Section Machine.

Variable C : costs.
Variable R : nat.
Variable CODE : addr -> val -> tx.
Variable CB : addr.
Variable BF : nat.

(** Cold surcharges and the write cost by transition. *)

Definition kcold (kk : key) (acc : list key) : nat :=
  if inkey kk acc then 0 else c_cold C.

Definition acold (a : addr) (aacc : list addr) : nat :=
  if inaddr a aacc then 0 else c_acold C.

Definition wcost (cv v : val) (cd : nat) : nat :=
  (if cv =? 0 then (if v =? 0 then c_sreset C else c_sset C)
   else c_sreset C) + cd.

Definition wref (cv v : val) : nat :=
  if negb (cv =? 0) && (v =? 0) then R else 0.

Arguments kcold : simpl never.
Arguments acold : simpl never.
Arguments wcost : simpl never.
Arguments wref : simpl never.

(** Out-of-gas (or out-of-fuel) halt: a frame revert charging nothing
    further.  Runs are invoked with fuel equal to the gas limit; with every
    cost at least one the fuel bound is never the binding constraint, which
    [runp_fuel_ge] proves. *)

Definition oog (gas : nat) (w : buffer) (cred deb : addr -> nat)
               (n bn nn : nat) (acc : list key) (aacc : list addr) : out :=
  Out [] [] [] w [] [] false 0 gas 0 cred deb n bn nn acc aacc.

Fixpoint runp (f gas : nat) (cur : addr) (t : tx)
              (rd : reader) (brd : breader) (nrd : nreader)
              (n bn nn : nat) (w : buffer)
              (cred deb : addr -> nat)
              (acc : list key) (aacc : list addr) : out :=
  match t with
  | TDone => Out [] [] [] w [] [] true 0 gas 0 cred deb n bn nn acc aacc
  | TRet v => Out [] [] [] w [] [] true v gas 0 cred deb n bn nn acc aacc
  | TRevert => Out [] [] [] w [] [] false 0 gas 0 cred deb n bn nn acc aacc
  | TWrite a v k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          match wlookup w (cur, a) with
          | Some cv =>
              if wcost cv v (kcold (cur, a) acc) <=? gas
              then
                let o := runp f' (gas - wcost cv v (kcold (cur, a) acc)) cur k
                              rd brd nrd n bn nn (((cur, a), v) :: w) cred deb
                              ((cur, a) :: acc) aacc in
                Out (o_slog o) (o_blog o) (o_nlog o) (o_buf o) (o_evs o)
                    (o_tvs o) (o_ok o) (o_ret o) (o_gas o)
                    (wref cv v + o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                    (o_acc o) (o_aacc o)
              else oog gas w cred deb n bn nn acc aacc
          | None =>
              let cv := rd n (cur, a) in
              if wcost cv v (kcold (cur, a) acc) <=? gas
              then
                let o := runp f' (gas - wcost cv v (kcold (cur, a) acc)) cur k
                              rd brd nrd (S n) bn nn (((cur, a), v) :: w)
                              cred deb ((cur, a) :: acc) aacc in
                Out (((cur, a), cv) :: o_slog o) (o_blog o) (o_nlog o)
                    (o_buf o) (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o)
                    (wref cv v + o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                    (o_acc o) (o_aacc o)
              else
                Out [((cur, a), cv)] [] [] w [] [] false 0 gas 0 cred deb
                    (S n) bn nn acc aacc
          end
      end
  | TRead a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_read C + kcold (cur, a) acc <=? gas
          then
            match wlookup w (cur, a) with
            | Some v =>
                runp f' (gas - (c_read C + kcold (cur, a) acc)) cur (k v)
                     rd brd nrd n bn nn w cred deb ((cur, a) :: acc) aacc
            | None =>
                let v := rd n (cur, a) in
                let o := runp f' (gas - (c_read C + kcold (cur, a) acc)) cur
                              (k v) rd brd nrd (S n) bn nn w cred deb
                              ((cur, a) :: acc) aacc in
                Out (((cur, a), v) :: o_slog o) (o_blog o) (o_nlog o) (o_buf o)
                    (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                    (o_acc o) (o_aacc o)
            end
          else oog gas w cred deb n bn nn acc aacc
      end
  | TBal a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_bal C + acold a aacc <=? gas
          then
            let raw := brd bn a in
            let o := runp f' (gas - (c_bal C + acold a aacc)) cur
                          (k (raw + cred a - deb a)) rd brd nrd
                          n (S bn) nn w cred deb acc (a :: aacc) in
            Out (o_slog o) ((a, raw) :: o_blog o) (o_nlog o) (o_buf o)
                (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                (o_acc o) (o_aacc o)
          else oog gas w cred deb n bn nn acc aacc
      end
  | TNonce a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_nonce C + acold a aacc <=? gas
          then
            let raw := nrd nn a in
            let o := runp f' (gas - (c_nonce C + acold a aacc)) cur (k raw)
                          rd brd nrd n bn (S nn) w cred deb acc (a :: aacc) in
            Out (o_slog o) (o_blog o) ((a, raw) :: o_nlog o) (o_buf o)
                (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                (o_acc o) (o_aacc o)
          else oog gas w cred deb n bn nn acc aacc
      end
  | TWhile a tst b k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_while C + kcold (cur, a) acc <=? gas
          then
            match wlookup w (cur, a) with
            | Some v =>
                if tst v
                then runp f' (gas - (c_while C + kcold (cur, a) acc)) cur
                          (tseq b (TWhile a tst b k)) rd brd nrd n bn nn w
                          cred deb ((cur, a) :: acc) aacc
                else runp f' (gas - (c_while C + kcold (cur, a) acc)) cur k
                          rd brd nrd n bn nn w cred deb
                          ((cur, a) :: acc) aacc
            | None =>
                let v := rd n (cur, a) in
                let o := if tst v
                         then runp f' (gas - (c_while C + kcold (cur, a) acc))
                                   cur (tseq b (TWhile a tst b k)) rd brd nrd
                                   (S n) bn nn w cred deb
                                   ((cur, a) :: acc) aacc
                         else runp f' (gas - (c_while C + kcold (cur, a) acc))
                                   cur k rd brd nrd (S n) bn nn w cred deb
                                   ((cur, a) :: acc) aacc in
                Out (((cur, a), v) :: o_slog o) (o_blog o) (o_nlog o) (o_buf o)
                    (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                    (o_acc o) (o_aacc o)
            end
          else oog gas w cred deb n bn nn acc aacc
      end
  | TEmit e k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_emit C <=? gas
          then
            let o := runp f' (gas - c_emit C) cur k rd brd nrd n bn nn w
                          cred deb acc aacc in
            Out (o_slog o) (o_blog o) (o_nlog o) (o_buf o) (e :: o_evs o)
                (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                (o_acc o) (o_aacc o)
          else oog gas w cred deb n bn nn acc aacc
      end
  | TPay d amt k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_pay C + acold d aacc <=? gas
          then
            let raw := brd bn cur in
            if amt <=? raw + cred cur - deb cur
            then
              let o := runp f' (gas - (c_pay C + acold d aacc)) cur (k true)
                            rd brd nrd n (S bn) nn w
                            (bupd cred d (cred d + amt))
                            (bupd deb cur (deb cur + amt)) acc (d :: aacc) in
              Out (o_slog o) ((cur, raw) :: o_blog o) (o_nlog o) (o_buf o)
                  (o_evs o) ((cur, d, amt) :: o_tvs o) (o_ok o) (o_ret o)
                  (o_gas o) (o_ref o) (o_cred o) (o_deb o)
                  (o_n o) (o_bn o) (o_nn o) (o_acc o) (o_aacc o)
            else
              let o := runp f' (gas - (c_pay C + acold d aacc)) cur (k false)
                            rd brd nrd n (S bn) nn w cred deb acc
                            (d :: aacc) in
              Out (o_slog o) ((cur, raw) :: o_blog o) (o_nlog o) (o_buf o)
                  (o_evs o) (o_tvs o) (o_ok o) (o_ret o) (o_gas o) (o_ref o)
                  (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
                  (o_acc o) (o_aacc o)
          else oog gas w cred deb n bn nn acc aacc
      end
  | TCall c arg amt k =>
      match f with
      | 0 => oog gas w cred deb n bn nn acc aacc
      | S f' =>
          if c_call C + acold c aacc <=? gas
          then
            match amt with
            | 0 =>
                let oc := runp f' (gas - (c_call C + acold c aacc)) c
                               (CODE c arg) rd brd nrd n bn nn w cred deb
                               acc (c :: aacc) in
                if o_ok oc
                then
                  let o2 := runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                 rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                 (o_buf oc) (o_cred oc) (o_deb oc)
                                 (o_acc oc) (o_aacc oc) in
                  Out (o_slog oc ++ o_slog o2) (o_blog oc ++ o_blog o2)
                      (o_nlog oc ++ o_nlog o2) (o_buf o2)
                      (o_evs oc ++ o_evs o2) (o_tvs oc ++ o_tvs o2)
                      (o_ok o2) (o_ret o2) (o_gas o2) (o_ref oc + o_ref o2)
                      (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
                      (o_acc o2) (o_aacc o2)
                else
                  let o2 := runp f' (o_gas oc) cur (k None) rd brd nrd
                                 (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                 acc (c :: aacc) in
                  Out (o_slog oc ++ o_slog o2) (o_blog oc ++ o_blog o2)
                      (o_nlog oc ++ o_nlog o2) (o_buf o2)
                      (o_evs o2) (o_tvs o2)
                      (o_ok o2) (o_ret o2) (o_gas o2) (o_ref o2)
                      (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
                      (o_acc o2) (o_aacc o2)
            | S _ =>
                let raw := brd bn cur in
                if amt <=? raw + cred cur - deb cur
                then
                  let oc := runp f' (gas - (c_call C + acold c aacc)) c
                                 (CODE c arg) rd brd nrd n (S bn) nn w
                                 (bupd cred c (cred c + amt))
                                 (bupd deb cur (deb cur + amt))
                                 acc (c :: aacc) in
                  if o_ok oc
                  then
                    let o2 := runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                   rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                   (o_buf oc) (o_cred oc) (o_deb oc)
                                   (o_acc oc) (o_aacc oc) in
                    Out (o_slog oc ++ o_slog o2)
                        ((cur, raw) :: o_blog oc ++ o_blog o2)
                        (o_nlog oc ++ o_nlog o2) (o_buf o2)
                        (o_evs oc ++ o_evs o2)
                        ((cur, c, amt) :: o_tvs oc ++ o_tvs o2)
                        (o_ok o2) (o_ret o2) (o_gas o2) (o_ref oc + o_ref o2)
                        (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
                        (o_acc o2) (o_aacc o2)
                  else
                    let o2 := runp f' (o_gas oc) cur (k None) rd brd nrd
                                   (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                   acc (c :: aacc) in
                    Out (o_slog oc ++ o_slog o2)
                        ((cur, raw) :: o_blog oc ++ o_blog o2)
                        (o_nlog oc ++ o_nlog o2) (o_buf o2)
                        (o_evs o2) (o_tvs o2)
                        (o_ok o2) (o_ret o2) (o_gas o2) (o_ref o2)
                        (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
                        (o_acc o2) (o_aacc o2)
                else
                  let o2 := runp f' (gas - (c_call C + acold c aacc)) cur
                                 (k None) rd brd nrd n (S bn) nn w cred deb
                                 acc (c :: aacc) in
                  Out (o_slog o2) ((cur, raw) :: o_blog o2) (o_nlog o2)
                      (o_buf o2) (o_evs o2) (o_tvs o2)
                      (o_ok o2) (o_ret o2) (o_gas o2) (o_ref o2)
                      (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
                      (o_acc o2) (o_aacc o2)
            end
          else oog gas w cred deb n bn nn acc aacc
      end
  end.

(** Case-split helper for goals over [runp]: splits the pending gas checks,
    buffer lookups, value matches, and branch tests that guard each
    execution case. *)

Ltac rsplit :=
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match wlookup ?w ?k with _ => _ end] =>
      destruct (wlookup w k) eqn:?
  | |- context [match ?a with 0 => _ | S _ => _ end] => destruct a eqn:?
  end.

(** A transaction runs with fuel equal to its gas limit, at its fee account,
    with fresh ordinals, an empty overlay, no credits, the upfront hold of
    its whole gas cost at the effective price, and the fee account and
    coinbase warm. *)

Definition deb0 (fee : addr) (hold : nat) : addr -> nat :=
  fun a => if a =? fee then hold else 0.

Definition zerof : addr -> nat := fun _ => 0.

Definition aacc0 (fee : addr) : list addr := [fee; CB].

Definition runt (i : item) (rd : reader) (brd : breader) (nrd : nreader) : out :=
  let '(fee, non, t, g, p) := i in
  runp g (g - c_base C) fee t rd brd nrd 0 0 0 [] zerof
       (deb0 fee (g * (BF + p))) [] (aacc0 fee).

(** ** Receipts, the admission gate, sequential execution

    The gate is checked against the true prefix machine before any
    execution: an admitted transaction covers the intrinsic cost within its
    limit, carries its account's exact next nonce, and funds its whole gas
    cost at the effective price, base fee plus tip.  A rejected transaction
    performs no run and leaves the machine untouched.  An executed
    transaction holds its whole gas cost, settles its recorded transfers,
    returns the unconsumed and refunded portion, pays the consumed portion's
    tip to the coinbase, burns the consumed portion's base fee, and bumps
    its nonce.  A reverted transaction pays for what it consumed with no
    refund. *)

Definition mach : Type := (storage * bank * nonces)%type.

Inductive status : Type := SOk | SRev | SRejected.

Definition rcpt : Type :=
  (status * nat * buffer * list val * list transfer)%type.

Definition rejrcpt : rcpt := (SRejected, 0, [], [], []).

Definition gateb (bk : bank) (nm : nonces) (i : item) : bool :=
  let '(fee, non, _, g, p) := i in
  (c_base C <=? g) && (non =? nm fee) && (g * (BF + p) <=? bk fee).

Definition finish (st : storage) (bk : bank) (nm : nonces)
                  (fee : addr) (g p : nat) (o : out) : mach * rcpt :=
  let u := g - o_gas o in
  if o_ok o
  then
    let u_eff := u - Nat.min (o_ref o) (u / 2) in
    let b1 := bupd bk fee (bk fee - g * (BF + p)) in
    let b2 := apply_tvs b1 (o_tvs o) in
    let b3 := bupd b2 fee (b2 fee + (g - u_eff) * (BF + p)) in
    let b4 := bupd b3 CB (b3 CB + u_eff * p) in
    ((commit st (o_buf o), b4, bupd nm fee (S (nm fee))),
     (SOk, u_eff, o_buf o, o_evs o, o_tvs o))
  else
    ((st, bupd (bupd bk fee (bk fee - u * (BF + p))) CB
               (bupd bk fee (bk fee - u * (BF + p)) CB + u * p),
      bupd nm fee (S (nm fee))),
     (SRev, u, [], [], [])).

Definition step (m : mach) (i : item) : mach * rcpt :=
  let '(st, bk, nm) := m in
  if gateb bk nm i
  then
    let '(fee, non, t, g, p) := i in
    finish st bk nm fee g p (runt i (of_state st) (of_bank bk) (of_nonces nm))
  else (m, rejrcpt).

Fixpoint seq_execr (m : mach) (ts : list item) : mach * list rcpt :=
  match ts with
  | [] => (m, [])
  | i :: rest =>
      let '(m1, r) := step m i in
      let '(m2, rs) := seq_execr m1 rest in
      (m2, r :: rs)
  end.

(** ** Validation *)

Fixpoint valid (s : storage) (log : list (key * val)) : bool :=
  match log with
  | [] => true
  | (k, v) :: rest => (s k =? v) && valid s rest
  end.

Fixpoint bvalid (b : bank) (log : list (addr * nat)) : bool :=
  match log with
  | [] => true
  | (a, v) :: rest => (b a =? v) && bvalid b rest
  end.

Definition nvalid : nonces -> list (addr * nat) -> bool := bvalid.

Lemma valid_true_In :
  forall log s,
    valid s log = true ->
    forall k v, In (k, v) log -> s k = v.
Proof.
  induction log as [| [k0 v0] rest IH]; simpl; intros s H k v Hin.
  - contradiction.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    destruct Hin as [Hin | Hin].
    + injection Hin as -> ->. apply Nat.eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma bvalid_true_In :
  forall log b,
    bvalid b log = true ->
    forall a v, In (a, v) log -> b a = v.
Proof.
  induction log as [| [a0 v0] rest IH]; simpl; intros b H a v Hin.
  - contradiction.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    destruct Hin as [Hin | Hin].
    + injection Hin as -> ->. apply Nat.eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma valid_app :
  forall l1 l2 s, valid s (l1 ++ l2) = valid s l1 && valid s l2.
Proof.
  induction l1 as [| [k v] r IH]; simpl; intros l2 s.
  - reflexivity.
  - rewrite IH. apply andb_assoc.
Qed.

Lemma bvalid_app :
  forall l1 l2 b, bvalid b (l1 ++ l2) = bvalid b l1 && bvalid b l2.
Proof.
  induction l1 as [| [a v] r IH]; simpl; intros l2 b.
  - reflexivity.
  - rewrite IH. apply andb_assoc.
Qed.

Lemma valid_stable :
  forall log (s s' : storage),
    valid s log = true ->
    (forall k, In k (map fst log) -> s' k = s k) ->
    valid s' log = true.
Proof.
  induction log as [| [k0 v0] rest IH]; simpl; intros s s' H Hag.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff. split.
    + rewrite (Hag k0 (or_introl eq_refl)). exact H1.
    + eapply IH; [exact H2 |].
      intros k Hin. apply Hag. right. exact Hin.
Qed.

Lemma bvalid_stable :
  forall log (b b' : bank),
    bvalid b log = true ->
    (forall a, In a (map fst log) -> b' a = b a) ->
    bvalid b' log = true.
Proof.
  induction log as [| [a0 v0] rest IH]; simpl; intros b b' H Hag.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff. split.
    + rewrite (Hag a0 (or_introl eq_refl)). exact H1.
    + eapply IH; [exact H2 |].
      intros a Hin. apply Hag. right. exact Hin.
Qed.

(** ** Validation and merge

    A speculation is a triple of read sources.  [cstep] is the single
    validate-or-re-execute step shared by the merge, the instrumented
    merge, the engine, and the operational commit: the gate is checked
    against the true prefix machine first, a rejected transaction consumes
    no execution at all; otherwise the storage log is validated against the
    merged prefix storage, the balance log against the merged prefix bank,
    the nonce log against the merged prefix nonces; agreement commits the
    speculative outcome unchanged, disagreement re-executes against the
    true prefix state.  The boolean is the conflict flag: true exactly when
    the position re-executed.  A missing speculation is an unspeculated
    first execution, not a conflict. *)

Definition spec : Type := (reader * breader * nreader)%type.

Definition vcheck (st : storage) (bk : bank) (nm : nonces) (o : out) : bool :=
  valid st (o_slog o) && bvalid bk (o_blog o) && nvalid nm (o_nlog o).

Definition cstep (m : mach) (i : item) (oo : option out) : (mach * rcpt) * bool :=
  let '(st, bk, nm) := m in
  if gateb bk nm i
  then
    match oo with
    | Some o =>
        if vcheck st bk nm o
        then let '(fee, non, t, g, p) := i in
             (finish st bk nm fee g p o, false)
        else (step m i, true)
    | None => (step m i, false)
    end
  else ((m, rejrcpt), false).

Definition spec_out (i : item) (sp : spec) : out :=
  let '(rd, brd, nrd) := sp in runt i rd brd nrd.

(** [mstep] additionally counts the executor invocations the merge performs
    at this position: one per validated speculation, two per conflicted
    position, one per position whose speculation is missing, none for a
    rejected transaction. *)

Definition mstep (m : mach) (i : item) (os : option spec)
  : (mach * rcpt) * bool * nat :=
  let '(mr, fl) := cstep m i (option_map (spec_out i) os) in
  let '(st, bk, nm) := m in
  (mr, fl,
   if gateb bk nm i
   then match os with Some _ => if fl then 2 else 1 | None => 1 end
   else 0).

Fixpoint omergeX (m : mach) (ts : list item) (specs : list spec)
  : mach * list rcpt * list bool * nat :=
  match ts with
  | [] => (m, [], [], 0)
  | i :: rest =>
      let '(mr, fl, x) := mstep m i (hd_error specs) in
      let '(m1, r) := mr in
      let '(m2, rs, fls, xs) := omergeX m1 rest (tl specs) in
      (m2, r :: rs, fl :: fls, x + xs)
  end.

Fixpoint count_true (l : list bool) : nat :=
  match l with
  | [] => 0
  | b :: r => (if b then 1 else 0) + count_true r
  end.

Definition omerge (m : mach) (ts : list item) (specs : list spec)
  : mach * list rcpt * nat :=
  let '(m2, rs, fls, _) := omergeX m ts specs in (m2, rs, count_true fls).

Definition executions (m : mach) (ts : list item) (specs : list spec) : nat :=
  snd (omergeX m ts specs).

Definition reexec_flags (m : mach) (ts : list item) (specs : list spec)
  : list bool :=
  snd (fst (omergeX m ts specs)).

(** ** Gas bound *)

Lemma runp_gas_bound :
  forall f gas cur t rd brd nrd n bn nn w cred deb acc aacc,
    o_gas (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc) <= gas.
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb acc aacc;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    simpl; try lia; rsplit; simpl; try lia;
    try (eapply Nat.le_trans; [apply IH | lia]);
    (eapply Nat.le_trans; [apply IH |];
     eapply Nat.le_trans; [apply IH | lia]).
Qed.

(** ** Replay

    A storage, bank, and nonce map agreeing with every logged read
    reproduce a run exactly: logs, buffer, events, transfers, revert
    decision, return value, gas, refunds, deltas, ordinals, and warmth,
    whatever the read sources were.  Buffer hits, transition costs and
    refunds, in-flight arithmetic, and frame decisions are functions of the
    logged values and the deterministic warm sets, so agreement on the logs
    pins the whole run. *)

Lemma replay :
  forall f gas cur t rd brd nrd n bn nn w cred deb acc aacc
         (s : storage) (b : bank) (nm : nonces),
    (forall k v, In (k, v) (o_slog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> s k = v) ->
    (forall a v, In (a, v) (o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> b a = v) ->
    (forall a v, In (a, v) (o_nlog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> nm a = v) ->
    runp f gas cur t (of_state s) (of_bank b) (of_nonces nm) n bn nn w cred deb acc aacc
    = runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc.
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb acc aacc s b nm Hs Hb Hn;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    try reflexivity; simpl in *.
  - (* TWrite *)
    destruct (wlookup w (cur, a)) as [cv |] eqn:Hw.
    + destruct (wcost cv v (kcold (cur, a) acc) <=? gas) eqn:Hg;
        [| reflexivity].
      simpl in Hs, Hb, Hn.
      rewrite (IH (gas - wcost cv v (kcold (cur, a) acc)) cur k rd brd nrd
                  n bn nn (((cur, a), v) :: w) cred deb ((cur, a) :: acc) aacc
                  s b nm Hs Hb Hn).
      reflexivity.
    + assert (Hv : s (cur, a) = rd n (cur, a)).
      { apply Hs. cbv zeta.
        destruct (wcost (rd n (cur, a)) v (kcold (cur, a) acc) <=? gas);
          left; reflexivity. }
      replace (of_state s n (cur, a)) with (rd n (cur, a))
        by (symmetry; exact Hv).
      cbv zeta.
      destruct (wcost (rd n (cur, a)) v (kcold (cur, a) acc) <=? gas) eqn:Hg.
      * assert (Hs' : forall k0 v0,
                   In (k0, v0)
                      (o_slog (runp f' (gas - wcost (rd n (cur, a)) v
                                              (kcold (cur, a) acc)) cur k
                                    rd brd nrd (S n) bn nn
                                    (((cur, a), v) :: w) cred deb
                                    ((cur, a) :: acc) aacc)) ->
                   s k0 = v0).
        { intros k0 v0 Hin. apply Hs. right. exact Hin. }
        assert (Hb' : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (gas - wcost (rd n (cur, a)) v
                                              (kcold (cur, a) acc)) cur k
                                    rd brd nrd (S n) bn nn
                                    (((cur, a), v) :: w) cred deb
                                    ((cur, a) :: acc) aacc)) ->
                   b a0 = v0).
        { intros a0 v0 Hin. apply Hb. exact Hin. }
        assert (Hn' : forall a0 v0,
                   In (a0, v0)
                      (o_nlog (runp f' (gas - wcost (rd n (cur, a)) v
                                              (kcold (cur, a) acc)) cur k
                                    rd brd nrd (S n) bn nn
                                    (((cur, a), v) :: w) cred deb
                                    ((cur, a) :: acc) aacc)) ->
                   nm a0 = v0).
        { intros a0 v0 Hin. apply Hn. exact Hin. }
        rewrite (IH (gas - wcost (rd n (cur, a)) v (kcold (cur, a) acc)) cur k
                    rd brd nrd (S n) bn nn (((cur, a), v) :: w) cred deb
                    ((cur, a) :: acc) aacc s b nm Hs' Hb' Hn').
        reflexivity.
      * reflexivity.
  - (* TRead *)
    destruct (c_read C + kcold (cur, a) acc <=? gas) eqn:Hg; [| reflexivity].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + simpl in Hs, Hb, Hn.
      apply (IH (gas - (c_read C + kcold (cur, a) acc)) cur (k v0) rd brd nrd
                n bn nn w cred deb ((cur, a) :: acc) aacc s b nm Hs Hb Hn).
    + simpl in Hs, Hb, Hn.
      assert (Hv : s (cur, a) = rd n (cur, a))
        by (apply Hs; left; reflexivity).
      replace (of_state s n (cur, a)) with (rd n (cur, a))
        by (symmetry; exact Hv).
      assert (Hs' : forall k0 v0,
                 In (k0, v0)
                    (o_slog (runp f' (gas - (c_read C + kcold (cur, a) acc))
                                  cur (k (rd n (cur, a))) rd brd nrd
                                  (S n) bn nn w cred deb
                                  ((cur, a) :: acc) aacc)) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. right. exact Hin. }
      rewrite (IH (gas - (c_read C + kcold (cur, a) acc)) cur
                  (k (rd n (cur, a))) rd brd nrd (S n) bn nn w cred deb
                  ((cur, a) :: acc) aacc s b nm Hs' Hb Hn).
      reflexivity.
  - (* TBal *)
    destruct (c_bal C + acold a aacc <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    assert (Hv : b a = brd bn a) by (apply Hb; left; reflexivity).
    replace (of_bank b bn a) with (brd bn a) by (symmetry; exact Hv).
    assert (Hb' : forall a0 v0,
               In (a0, v0)
                  (o_blog (runp f' (gas - (c_bal C + acold a aacc)) cur
                                (k (brd bn a + cred a - deb a))
                                rd brd nrd n (S bn) nn w cred deb
                                acc (a :: aacc))) ->
               b a0 = v0).
    { intros a0 v0 Hin. apply Hb. right. exact Hin. }
    rewrite (IH (gas - (c_bal C + acold a aacc)) cur
                (k (brd bn a + cred a - deb a)) rd brd nrd
                n (S bn) nn w cred deb acc (a :: aacc) s b nm Hs Hb' Hn).
    reflexivity.
  - (* TNonce *)
    destruct (c_nonce C + acold a aacc <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    assert (Hv : nm a = nrd nn a) by (apply Hn; left; reflexivity).
    replace (of_nonces nm nn a) with (nrd nn a) by (symmetry; exact Hv).
    assert (Hn' : forall a0 v0,
               In (a0, v0)
                  (o_nlog (runp f' (gas - (c_nonce C + acold a aacc)) cur
                                (k (nrd nn a)) rd brd nrd
                                n bn (S nn) w cred deb acc (a :: aacc))) ->
               nm a0 = v0).
    { intros a0 v0 Hin. apply Hn. right. exact Hin. }
    rewrite (IH (gas - (c_nonce C + acold a aacc)) cur (k (nrd nn a)) rd brd nrd
                n bn (S nn) w cred deb acc (a :: aacc) s b nm Hs Hb Hn').
    reflexivity.
  - (* TWhile *)
    destruct (c_while C + kcold (cur, a) acc <=? gas) eqn:Hg; [| reflexivity].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + simpl in Hs, Hb, Hn.
      destruct (tst v0) eqn:Hz.
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                  (tseq tb (TWhile a tst tb k)) rd brd nrd n bn nn w cred deb
                  ((cur, a) :: acc) aacc s b nm Hs Hb Hn).
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd nrd
                  n bn nn w cred deb ((cur, a) :: acc) aacc s b nm Hs Hb Hn).
    + simpl in Hs, Hb, Hn.
      assert (Hv : s (cur, a) = rd n (cur, a))
        by (apply Hs; left; reflexivity).
      replace (of_state s n (cur, a)) with (rd n (cur, a))
        by (symmetry; exact Hv).
      assert (Hs' : forall k0 v0,
                 In (k0, v0)
                    (o_slog (if tst (rd n (cur, a))
                             then runp f'
                                    (gas - (c_while C + kcold (cur, a) acc))
                                    cur (tseq tb (TWhile a tst tb k)) rd brd
                                    nrd (S n) bn nn w cred deb
                                    ((cur, a) :: acc) aacc
                             else runp f'
                                    (gas - (c_while C + kcold (cur, a) acc))
                                    cur k rd brd nrd (S n) bn nn w cred deb
                                    ((cur, a) :: acc) aacc)) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. right. exact Hin. }
      destruct (tst (rd n (cur, a))) eqn:Hz.
      * rewrite (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                    (tseq tb (TWhile a tst tb k)) rd brd nrd
                    (S n) bn nn w cred deb ((cur, a) :: acc) aacc s b nm
                    Hs' Hb Hn).
        reflexivity.
      * rewrite (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd nrd
                    (S n) bn nn w cred deb ((cur, a) :: acc) aacc s b nm
                    Hs' Hb Hn).
        reflexivity.
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    rewrite (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb acc aacc
                s b nm Hs Hb Hn).
    reflexivity.
  - (* TPay *)
    destruct (c_pay C + acold d aacc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hv : b cur = brd bn cur).
    { apply Hb.
      destruct (amt <=? brd bn cur + cred cur - deb cur); simpl; left;
        reflexivity. }
    replace (of_bank b bn cur) with (brd bn cur) by (symmetry; exact Hv).
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp;
      simpl in Hs, Hb, Hn.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - (c_pay C + acold d aacc)) cur
                                  (k true) rd brd nrd n (S bn) nn w
                                  (bupd cred d (cred d + amt))
                                  (bupd deb cur (deb cur + amt))
                                  acc (d :: aacc))) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      rewrite (IH (gas - (c_pay C + acold d aacc)) cur (k true) rd brd nrd
                  n (S bn) nn w (bupd cred d (cred d + amt))
                  (bupd deb cur (deb cur + amt)) acc (d :: aacc)
                  s b nm Hs Hb' Hn).
      reflexivity.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - (c_pay C + acold d aacc)) cur
                                  (k false) rd brd nrd n (S bn) nn w cred deb
                                  acc (d :: aacc))) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      rewrite (IH (gas - (c_pay C + acold d aacc)) cur (k false) rd brd nrd
                  n (S bn) nn w cred deb acc (d :: aacc) s b nm Hs Hb' Hn).
      reflexivity.
  - (* TCall *)
    destruct (c_call C + acold c aacc <=? gas) eqn:Hg; [| reflexivity].
    destruct amt as [| amt'].
    + (* no value *)
      set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                      rd brd nrd n bn nn w cred deb acc (c :: aacc)) in *.
      destruct (o_ok oc) eqn:Hok; simpl in Hs, Hb, Hn.
      * assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
        { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
        assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
        assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
        { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
        assert (Ec : runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                          (of_state s) (of_bank b) (of_nonces nm)
                          n bn nn w cred deb acc (c :: aacc) = oc).
        { apply (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                    rd brd nrd n bn nn w cred deb acc (c :: aacc)
                    s b nm Hsc Hbc Hnc). }
        rewrite Ec, Hok.
        assert (Hs2 : forall k0 v0,
                   In (k0, v0)
                      (o_slog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                    rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                    (o_buf oc) (o_cred oc) (o_deb oc)
                                    (o_acc oc) (o_aacc oc))) ->
                   s k0 = v0).
        { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
        assert (Hb2 : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                    rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                    (o_buf oc) (o_cred oc) (o_deb oc)
                                    (o_acc oc) (o_aacc oc))) ->
                   b a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
        assert (Hn2 : forall a0 v0,
                   In (a0, v0)
                      (o_nlog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                    rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                    (o_buf oc) (o_cred oc) (o_deb oc)
                                    (o_acc oc) (o_aacc oc))) ->
                   nm a0 = v0).
        { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
        rewrite (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                    (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                    (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc) s b nm
                    Hs2 Hb2 Hn2).
        reflexivity.
      * assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
        { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
        assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
        assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
        { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
        assert (Ec : runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                          (of_state s) (of_bank b) (of_nonces nm)
                          n bn nn w cred deb acc (c :: aacc) = oc).
        { apply (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                    rd brd nrd n bn nn w cred deb acc (c :: aacc)
                    s b nm Hsc Hbc Hnc). }
        rewrite Ec, Hok.
        assert (Hs2 : forall k0 v0,
                   In (k0, v0)
                      (o_slog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                    acc (c :: aacc))) ->
                   s k0 = v0).
        { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
        assert (Hb2 : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                    acc (c :: aacc))) ->
                   b a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
        assert (Hn2 : forall a0 v0,
                   In (a0, v0)
                      (o_nlog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                    acc (c :: aacc))) ->
                   nm a0 = v0).
        { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
        rewrite (IH (o_gas oc) cur (k None) rd brd nrd
                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc (c :: aacc)
                    s b nm Hs2 Hb2 Hn2).
        reflexivity.
    + (* value-carrying *)
      assert (Hv : b cur = brd bn cur).
      { apply Hb.
        destruct (S amt' <=? brd bn cur + cred cur - deb cur).
        - destruct (o_ok (runp f' (gas - (c_call C + acold c aacc)) c
                               (CODE c arg) rd brd nrd n (S bn) nn w
                               (bupd cred c (cred c + S amt'))
                               (bupd deb cur (deb cur + S amt'))
                               acc (c :: aacc)));
            simpl; left; reflexivity.
        - simpl; left; reflexivity. }
      replace (of_bank b bn cur) with (brd bn cur) by (symmetry; exact Hv).
      destruct (S amt' <=? brd bn cur + cred cur - deb cur) eqn:Hp.
      * set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                        rd brd nrd n (S bn) nn w
                        (bupd cred c (cred c + S amt'))
                        (bupd deb cur (deb cur + S amt'))
                        acc (c :: aacc)) in *.
        destruct (o_ok oc) eqn:Hok; simpl in Hs, Hb, Hn.
        -- assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
           { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
           assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. left.
             exact Hin. }
           assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
           { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
           assert (Ec : runp f' (gas - (c_call C + acold c aacc)) c
                             (CODE c arg) (of_state s) (of_bank b)
                             (of_nonces nm) n (S bn) nn w
                             (bupd cred c (cred c + S amt'))
                             (bupd deb cur (deb cur + S amt'))
                             acc (c :: aacc) = oc).
           { apply (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                       rd brd nrd n (S bn) nn w
                       (bupd cred c (cred c + S amt'))
                       (bupd deb cur (deb cur + S amt'))
                       acc (c :: aacc) s b nm Hsc Hbc Hnc). }
           rewrite Ec, Hok.
           assert (Hs2 : forall k0 v0,
                      In (k0, v0)
                         (o_slog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                       rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                       (o_buf oc) (o_cred oc) (o_deb oc)
                                       (o_acc oc) (o_aacc oc))) ->
                      s k0 = v0).
           { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
           assert (Hb2 : forall a0 v0,
                      In (a0, v0)
                         (o_blog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                       rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                       (o_buf oc) (o_cred oc) (o_deb oc)
                                       (o_acc oc) (o_aacc oc))) ->
                      b a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. right.
             exact Hin. }
           assert (Hn2 : forall a0 v0,
                      In (a0, v0)
                         (o_nlog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                       rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                       (o_buf oc) (o_cred oc) (o_deb oc)
                                       (o_acc oc) (o_aacc oc))) ->
                      nm a0 = v0).
           { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
           rewrite (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                       (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                       (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc) s b nm
                       Hs2 Hb2 Hn2).
           reflexivity.
        -- assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
           { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
           assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. left.
             exact Hin. }
           assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
           { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
           assert (Ec : runp f' (gas - (c_call C + acold c aacc)) c
                             (CODE c arg) (of_state s) (of_bank b)
                             (of_nonces nm) n (S bn) nn w
                             (bupd cred c (cred c + S amt'))
                             (bupd deb cur (deb cur + S amt'))
                             acc (c :: aacc) = oc).
           { apply (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                       rd brd nrd n (S bn) nn w
                       (bupd cred c (cred c + S amt'))
                       (bupd deb cur (deb cur + S amt'))
                       acc (c :: aacc) s b nm Hsc Hbc Hnc). }
           rewrite Ec, Hok.
           assert (Hs2 : forall k0 v0,
                      In (k0, v0)
                         (o_slog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                       acc (c :: aacc))) ->
                      s k0 = v0).
           { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
           assert (Hb2 : forall a0 v0,
                      In (a0, v0)
                         (o_blog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                       acc (c :: aacc))) ->
                      b a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. right.
             exact Hin. }
           assert (Hn2 : forall a0 v0,
                      In (a0, v0)
                         (o_nlog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                       acc (c :: aacc))) ->
                      nm a0 = v0).
           { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
           rewrite (IH (o_gas oc) cur (k None) rd brd nrd
                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc
                       (c :: aacc) s b nm Hs2 Hb2 Hn2).
           reflexivity.
      * simpl in Hs, Hb, Hn.
        assert (Hb' : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (gas - (c_call C + acold c aacc)) cur
                                    (k None) rd brd nrd n (S bn) nn w cred deb
                                    acc (c :: aacc))) ->
                   b a0 = v0).
        { intros a0 v0 Hin. apply Hb. right. exact Hin. }
        rewrite (IH (gas - (c_call C + acold c aacc)) cur (k None) rd brd nrd
                    n (S bn) nn w cred deb acc (c :: aacc) s b nm Hs Hb' Hn).
        reflexivity.
Qed.

(** ** Self-validation, one source at a time *)

Lemma valid_self_s :
  forall f gas cur t (s : storage) brd nrd n bn nn w cred deb acc aacc,
    valid s (o_slog (runp f gas cur t (of_state s) brd nrd n bn nn w cred deb acc aacc))
    = true.
Proof.
  induction f as [| f' IH];
    intros gas cur t s brd nrd n bn nn w cred deb acc aacc;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; try (apply IH); reflexivity);
    (rewrite valid_app; rewrite !IH; reflexivity).
Qed.

Lemma bvalid_self_b :
  forall f gas cur t rd (b : bank) nrd n bn nn w cred deb acc aacc,
    bvalid b (o_blog (runp f gas cur t rd (of_bank b) nrd n bn nn w cred deb acc aacc))
    = true.
Proof.
  induction f as [| f' IH];
    intros gas cur t rd b nrd n bn nn w cred deb acc aacc;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; try (apply IH); reflexivity);
    try (rewrite bvalid_app; rewrite !IH; reflexivity);
    (rewrite Nat.eqb_refl; simpl; rewrite bvalid_app; rewrite !IH;
     reflexivity).
Qed.

Lemma nvalid_self_n :
  forall f gas cur t rd brd (nm : nonces) n bn nn w cred deb acc aacc,
    nvalid nm (o_nlog (runp f gas cur t rd brd (of_nonces nm) n bn nn w cred deb acc aacc))
    = true.
Proof.
  unfold nvalid.
  induction f as [| f' IH];
    intros gas cur t rd brd nm n bn nn w cred deb acc aacc;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; try (apply IH); reflexivity);
    (rewrite bvalid_app; rewrite !IH; reflexivity).
Qed.

(** ** In-flight settlement soundness

    Along any run whose logged balance reads agree with a bank [B], the
    in-flight discipline is exact: the recorded transfers, including value
    attached to calls, settle stepwise against the tracked bank without
    truncation, and settlement lands on the bank described by the final
    deltas.  The invariant is stated additively, so nat subtraction never
    bites. *)

Definition inflight_inv (B bc : bank) (cred deb : addr -> nat) : Prop :=
  forall a, bc a + deb a = B a + cred a.

Lemma inflight_sound :
  forall f gas cur t rd brd nrd n bn nn w cred deb acc aacc (B bc : bank),
    (forall a v, In (a, v) (o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> B a = v) ->
    inflight_inv B bc cred deb ->
    apply_ok bc (o_tvs (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) = true
    /\ inflight_inv B
         (apply_tvs bc (o_tvs (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)))
         (o_cred (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc))
         (o_deb (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)).
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb acc aacc B bc Hb Hinv;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    simpl in *;
    try (split; [reflexivity | exact Hinv]).
  - (* TWrite *)
    destruct (wlookup w (cur, a)) as [cv |] eqn:Hw.
    + destruct (wcost cv v (kcold (cur, a) acc) <=? gas) eqn:Hg;
        [| split; [reflexivity | exact Hinv]].
      simpl in Hb.
      apply (IH (gas - wcost cv v (kcold (cur, a) acc)) cur k rd brd nrd
                n bn nn (((cur, a), v) :: w) cred deb ((cur, a) :: acc) aacc
                B bc Hb Hinv).
    + destruct (wcost (rd n (cur, a)) v (kcold (cur, a) acc) <=? gas) eqn:Hg.
      * simpl in Hb.
        apply (IH (gas - wcost (rd n (cur, a)) v (kcold (cur, a) acc)) cur k
                  rd brd nrd (S n) bn nn (((cur, a), v) :: w) cred deb
                  ((cur, a) :: acc) aacc B bc Hb Hinv).
      * split; [reflexivity | exact Hinv].
  - (* TRead *)
    destruct (c_read C + kcold (cur, a) acc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw; simpl in Hb.
    + apply (IH (gas - (c_read C + kcold (cur, a) acc)) cur (k v0) rd brd nrd
                n bn nn w cred deb ((cur, a) :: acc) aacc B bc Hb Hinv).
    + apply (IH (gas - (c_read C + kcold (cur, a) acc)) cur
                (k (rd n (cur, a))) rd brd nrd (S n) bn nn w cred deb
                ((cur, a) :: acc) aacc B bc Hb Hinv).
  - (* TBal *)
    destruct (c_bal C + acold a aacc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    assert (Hb' : forall a0 v0,
               In (a0, v0)
                  (o_blog (runp f' (gas - (c_bal C + acold a aacc)) cur
                                (k (brd bn a + cred a - deb a))
                                rd brd nrd n (S bn) nn w cred deb
                                acc (a :: aacc))) ->
               B a0 = v0).
    { intros a0 v0 Hin. apply Hb. right. exact Hin. }
    apply (IH (gas - (c_bal C + acold a aacc)) cur
              (k (brd bn a + cred a - deb a)) rd brd nrd n (S bn) nn w
              cred deb acc (a :: aacc) B bc Hb' Hinv).
  - (* TNonce *)
    destruct (c_nonce C + acold a aacc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    apply (IH (gas - (c_nonce C + acold a aacc)) cur (k (nrd nn a)) rd brd nrd
              n bn (S nn) w cred deb acc (a :: aacc) B bc Hb Hinv).
  - (* TWhile *)
    destruct (c_while C + kcold (cur, a) acc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw; simpl in Hb.
    + destruct (tst v0) eqn:Hz.
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                  (tseq tb (TWhile a tst tb k)) rd brd nrd n bn nn w cred deb
                  ((cur, a) :: acc) aacc B bc Hb Hinv).
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd nrd
                  n bn nn w cred deb ((cur, a) :: acc) aacc B bc Hb Hinv).
    + destruct (tst (rd n (cur, a))) eqn:Hz.
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                  (tseq tb (TWhile a tst tb k)) rd brd nrd (S n) bn nn w
                  cred deb ((cur, a) :: acc) aacc B bc Hb Hinv).
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd nrd
                  (S n) bn nn w cred deb ((cur, a) :: acc) aacc B bc Hb Hinv).
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    apply (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb acc aacc
              B bc Hb Hinv).
  - (* TPay *)
    destruct (c_pay C + acold d aacc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    assert (HB : B cur = brd bn cur).
    { apply Hb.
      destruct (amt <=? brd bn cur + cred cur - deb cur); simpl; left;
        reflexivity. }
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp; simpl in Hb.
    + apply Nat.leb_le in Hp.
      assert (Hbcur : bc cur = brd bn cur + cred cur - deb cur).
      { pose proof (Hinv cur) as Hc. rewrite HB in Hc. lia. }
      assert (Hamt : amt <= bc cur) by lia.
      assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - (c_pay C + acold d aacc)) cur
                                  (k true) rd brd nrd n (S bn) nn w
                                  (bupd cred d (cred d + amt))
                                  (bupd deb cur (deb cur + amt))
                                  acc (d :: aacc))) ->
                 B a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      assert (Hinv' : inflight_inv B
                        (bupd (bupd bc cur (bc cur - amt)) d
                              (bupd bc cur (bc cur - amt) d + amt))
                        (bupd cred d (cred d + amt))
                        (bupd deb cur (deb cur + amt))).
      { intros a0.
        pose proof (Hinv a0) as Ha0. pose proof (Hinv cur) as Hc.
        pose proof (Hinv d) as Hd.
        unfold bupd.
        destruct (Nat.eqb a0 d) eqn:Had;
          destruct (Nat.eqb a0 cur) eqn:Hac;
          destruct (Nat.eqb d cur) eqn:Hdc;
          repeat match goal with
                 | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
                 | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
                 end;
          lia. }
      destruct (IH (gas - (c_pay C + acold d aacc)) cur (k true) rd brd nrd
                   n (S bn) nn w (bupd cred d (cred d + amt))
                   (bupd deb cur (deb cur + amt)) acc (d :: aacc)
                   B (bupd (bupd bc cur (bc cur - amt)) d
                           (bupd bc cur (bc cur - amt) d + amt))
                   Hb' Hinv') as [Hok2 Hinv2].
      split.
      * simpl. apply andb_true_iff. split; [apply Nat.leb_le; exact Hamt |].
        exact Hok2.
      * simpl. exact Hinv2.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - (c_pay C + acold d aacc)) cur
                                  (k false) rd brd nrd n (S bn) nn w cred deb
                                  acc (d :: aacc))) ->
                 B a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      apply (IH (gas - (c_pay C + acold d aacc)) cur (k false) rd brd nrd
                n (S bn) nn w cred deb acc (d :: aacc) B bc Hb' Hinv).
  - (* TCall *)
    destruct (c_call C + acold c aacc <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    destruct amt as [| amt'].
    + (* no value *)
      set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                      rd brd nrd n bn nn w cred deb acc (c :: aacc)) in *.
      destruct (o_ok oc) eqn:Hok; simpl in Hb.
      * assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> B a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
        destruct (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                     rd brd nrd n bn nn w cred deb acc (c :: aacc)
                     B bc Hbc Hinv) as [Hokc Hinvc].
        fold oc in Hokc, Hinvc.
        assert (Hb2 : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                    rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                    (o_buf oc) (o_cred oc) (o_deb oc)
                                    (o_acc oc) (o_aacc oc))) ->
                   B a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
        destruct (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                     (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                     (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc)
                     B (apply_tvs bc (o_tvs oc)) Hb2 Hinvc) as [Hok2 Hinv2].
        split.
        -- simpl. rewrite apply_ok_app. apply andb_true_iff.
           split; [exact Hokc |]. exact Hok2.
        -- simpl. rewrite apply_app. exact Hinv2.
      * assert (Hb2 : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                    acc (c :: aacc))) ->
                   B a0 = v0).
        { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
        apply (IH (o_gas oc) cur (k None) rd brd nrd (o_n oc) (o_bn oc)
                  (o_nn oc) w cred deb acc (c :: aacc) B bc Hb2 Hinv).
    + (* value-carrying *)
      assert (HB : B cur = brd bn cur).
      { apply Hb.
        destruct (S amt' <=? brd bn cur + cred cur - deb cur).
        - destruct (o_ok (runp f' (gas - (c_call C + acold c aacc)) c
                               (CODE c arg) rd brd nrd n (S bn) nn w
                               (bupd cred c (cred c + S amt'))
                               (bupd deb cur (deb cur + S amt'))
                               acc (c :: aacc)));
            simpl; left; reflexivity.
        - simpl; left; reflexivity. }
      destruct (S amt' <=? brd bn cur + cred cur - deb cur) eqn:Hp.
      * apply Nat.leb_le in Hp.
        assert (Hbcur : bc cur = brd bn cur + cred cur - deb cur).
        { pose proof (Hinv cur) as Hc. rewrite HB in Hc. lia. }
        assert (Hamt : S amt' <= bc cur) by lia.
        assert (Hinv' : inflight_inv B
                          (bupd (bupd bc cur (bc cur - S amt')) c
                                (bupd bc cur (bc cur - S amt') c + S amt'))
                          (bupd cred c (cred c + S amt'))
                          (bupd deb cur (deb cur + S amt'))).
        { intros a0.
          pose proof (Hinv a0) as Ha0. pose proof (Hinv cur) as Hc.
          pose proof (Hinv c) as Hd.
          unfold bupd.
          destruct (Nat.eqb a0 c) eqn:Had;
            destruct (Nat.eqb a0 cur) eqn:Hac;
            destruct (Nat.eqb c cur) eqn:Hdc;
            repeat match goal with
                   | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
                   | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
                   end;
            lia. }
        set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                        rd brd nrd n (S bn) nn w
                        (bupd cred c (cred c + S amt'))
                        (bupd deb cur (deb cur + S amt'))
                        acc (c :: aacc)) in *.
        set (bc' := bupd (bupd bc cur (bc cur - S amt')) c
                         (bupd bc cur (bc cur - S amt') c + S amt')) in *.
        destruct (o_ok oc) eqn:Hok; simpl in Hb.
        -- assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> B a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. left.
             exact Hin. }
           destruct (IH (gas - (c_call C + acold c aacc)) c (CODE c arg)
                        rd brd nrd n (S bn) nn w
                        (bupd cred c (cred c + S amt'))
                        (bupd deb cur (deb cur + S amt'))
                        acc (c :: aacc) B bc' Hbc Hinv') as [Hokc Hinvc].
           fold oc in Hokc, Hinvc.
           assert (Hb2 : forall a0 v0,
                      In (a0, v0)
                         (o_blog (runp f' (o_gas oc) cur (k (Some (o_ret oc)))
                                       rd brd nrd (o_n oc) (o_bn oc) (o_nn oc)
                                       (o_buf oc) (o_cred oc) (o_deb oc)
                                       (o_acc oc) (o_aacc oc))) ->
                      B a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. right.
             exact Hin. }
           destruct (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                        (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                        (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc)
                        B (apply_tvs bc' (o_tvs oc)) Hb2 Hinvc)
             as [Hok2 Hinv2].
           split.
           ++ simpl. apply andb_true_iff.
              split; [exact (proj2 (Nat.leb_le (S amt') (bc cur)) Hamt) |].
              rewrite apply_ok_app. apply andb_true_iff.
              split; [exact Hokc |]. exact Hok2.
           ++ simpl. rewrite apply_app. exact Hinv2.
        -- assert (Hb2 : forall a0 v0,
                      In (a0, v0)
                         (o_blog (runp f' (o_gas oc) cur (k None) rd brd nrd
                                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb
                                       acc (c :: aacc))) ->
                      B a0 = v0).
           { intros a0 v0 Hin. apply Hb. right. apply in_or_app. right.
             exact Hin. }
           apply (IH (o_gas oc) cur (k None) rd brd nrd (o_n oc) (o_bn oc)
                     (o_nn oc) w cred deb acc (c :: aacc) B bc Hb2 Hinv).
      * simpl in Hb.
        assert (Hb2 : forall a0 v0,
                   In (a0, v0)
                      (o_blog (runp f' (gas - (c_call C + acold c aacc)) cur
                                    (k None) rd brd nrd n (S bn) nn w cred deb
                                    acc (c :: aacc))) ->
                   B a0 = v0).
        { intros a0 v0 Hin. apply Hb. right. exact Hin. }
        apply (IH (gas - (c_call C + acold c aacc)) cur (k None) rd brd nrd
                  n (S bn) nn w cred deb acc (c :: aacc) B bc Hb2 Hinv).
Qed.

(** ** Replay at the transaction level *)

Lemma replay_runt :
  forall i rd brd nrd (st : storage) (bk : bank) (nm : nonces),
    valid st (o_slog (runt i rd brd nrd)) = true ->
    bvalid bk (o_blog (runt i rd brd nrd)) = true ->
    nvalid nm (o_nlog (runt i rd brd nrd)) = true ->
    runt i (of_state st) (of_bank bk) (of_nonces nm) = runt i rd brd nrd.
Proof.
  intros [[[[fee non] t] g] p] rd brd nrd st bk nm Hv Hb Hn.
  unfold runt in *.
  apply replay.
  - exact (valid_true_In _ _ Hv).
  - exact (bvalid_true_In _ _ Hb).
  - exact (bvalid_true_In _ _ Hn).
Qed.

(** ** The merge step is the sequential step

    [cstep] commits validated speculative outcomes unchanged; replay makes
    the committed machine and receipt those of the sequential step, for any
    outcome that is some run of the position's own item. *)

Lemma cstep_state :
  forall m i oo,
    (forall o, oo = Some o ->
       exists rd, exists brd, exists nrd, o = runt i rd brd nrd) ->
    fst (cstep m i oo) = step m i.
Proof.
  intros [[st bk] nm] [[[[fee non] t] g] p] oo Hprov.
  unfold cstep.
  destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
  - destruct oo as [o |].
    + destruct (vcheck st bk nm o) eqn:Hv.
      * destruct (Hprov o eq_refl) as [rd [brd [nrd Ho]]]. subst o.
        unfold vcheck in Hv.
        apply andb_true_iff in Hv. destruct Hv as [Hv1 Hvn].
        apply andb_true_iff in Hv1. destruct Hv1 as [Hvs Hvb].
        cbn [fst]. unfold step. rewrite Hgate.
        rewrite (replay_runt (fee, non, t, g, p) rd brd nrd st bk nm
                   Hvs Hvb Hvn).
        reflexivity.
      * cbn [fst]. reflexivity.
    + cbn [fst]. reflexivity.
  - cbn [fst]. unfold step. rewrite Hgate. reflexivity.
Qed.

Lemma mstep_state :
  forall m i os, fst (fst (mstep m i os)) = step m i.
Proof.
  intros m i os.
  unfold mstep.
  assert (Hprov : forall o, option_map (spec_out i) os = Some o ->
             exists rd, exists brd, exists nrd, o = runt i rd brd nrd).
  { intros o Ho. destruct os as [[[rd brd] nrd] |]; [| discriminate].
    cbn in Ho. injection Ho as <-.
    exists rd, brd, nrd. reflexivity. }
  pose proof (cstep_state m i (option_map (spec_out i) os) Hprov) as Hc.
  destruct (cstep m i (option_map (spec_out i) os)) as [mr fl].
  destruct m as [[st bk] nm].
  cbn [fst] in *. exact Hc.
Qed.

(** ** Main theorem: merged execution is sequential execution *)

Theorem optimistic_correct :
  forall ts specs m,
    fst (omerge m ts specs) = seq_execr m ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - reflexivity.
  - unfold omerge in *. cbn [omergeX seq_execr].
    pose proof (mstep_state m i (hd_error specs)) as Hms.
    destruct (mstep m i (hd_error specs)) as [[[m1 r] fl] x].
    cbn [fst] in Hms.
    rewrite <- Hms.
    specialize (IH (tl specs) m1).
    destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
    cbn [fst] in IH. rewrite <- IH.
    reflexivity.
Qed.

Corollary speculation_irrelevant :
  forall ts specs1 specs2 m,
    fst (omerge m ts specs1) = fst (omerge m ts specs2).
Proof.
  intros ts specs1 specs2 m.
  rewrite (optimistic_correct ts specs1 m).
  rewrite (optimistic_correct ts specs2 m).
  reflexivity.
Qed.

(** ** The perfect-speculation fast path *)

Definition spec_of (m : mach) : spec :=
  (of_state (fst (fst m)), of_bank (snd (fst m)), of_nonces (snd m)).

Fixpoint prefix_specs (m : mach) (ts : list item) : list spec :=
  match ts with
  | [] => []
  | i :: rest => spec_of m :: prefix_specs (fst (step m i)) rest
  end.

Theorem fast_path :
  forall ts m,
    omerge m ts (prefix_specs m ts) = (seq_execr m ts, 0).
Proof.
  induction ts as [| i rest IH]; intros m.
  - reflexivity.
  - destruct m as [[st bk] nm]. destruct i as [[[[fee non] t] g] p].
    unfold omerge in *.
    cbn [omergeX seq_execr prefix_specs hd_error tl].
    unfold mstep, cstep.
    cbn [option_map spec_out spec_of fst snd].
    destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
    + assert (Hv : vcheck st bk nm
                     (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                           (of_nonces nm)) = true).
      { unfold vcheck, runt. cbv beta iota zeta.
        rewrite valid_self_s, bvalid_self_b, nvalid_self_n.
        reflexivity. }
      rewrite Hv.
      assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = finish st bk nm fee g p
                          (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (finish st bk nm fee g p
                  (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                        (of_nonces nm))) as [m1 r].
      cbn [fst].
      specialize (IH m1).
      destruct (omergeX m1 rest (prefix_specs m1 rest)) as [[[m2 rs] fls] xs].
      injection IH as IH1 IH2.
      rewrite <- IH1. cbn [count_true]. rewrite IH2.
      reflexivity.
    + assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = ((st, bk, nm), rejrcpt)).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      cbn [fst].
      specialize (IH (st, bk, nm)).
      destruct (omergeX (st, bk, nm) rest (prefix_specs (st, bk, nm) rest))
        as [[[m2 rs] fls] xs].
      injection IH as IH1 IH2.
      rewrite <- IH1. cbn [count_true]. rewrite IH2.
      reflexivity.
Qed.

(** ** Aggregate re-execution bound and per-position flags *)

Lemma omergeX_len :
  forall ts specs m,
    length (snd (fst (fst (omergeX m ts specs)))) = length ts /\
    length (snd (fst (omergeX m ts specs))) = length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. auto.
  - cbn [omergeX].
    destruct (mstep m i (hd_error specs)) as [[[m1 r] fl] x].
    specialize (IH (tl specs) m1).
    destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
    cbn [fst snd length] in *. destruct IH as [IH1 IH2].
    split; congruence.
Qed.

Lemma count_true_le : forall l, count_true l <= length l.
Proof.
  induction l as [| b r IH]; cbn; [lia | destruct b; lia].
Qed.

Theorem reexec_bound :
  forall ts specs m, snd (omerge m ts specs) <= length ts.
Proof.
  intros ts specs m. unfold omerge.
  pose proof (omergeX_len ts specs m) as [_ Hlen].
  destruct (omergeX m ts specs) as [[[m2 rs] fls] xs].
  cbn [snd fst] in *.
  rewrite <- Hlen. apply count_true_le.
Qed.

Theorem reexec_per_tx :
  forall ts specs m,
    snd (omerge m ts specs) = count_true (reexec_flags m ts specs)
    /\ length (reexec_flags m ts specs) = length ts.
Proof.
  intros ts specs m. unfold omerge, reexec_flags.
  pose proof (omergeX_len ts specs m) as [_ Hlen].
  destruct (omergeX m ts specs) as [[[m2 rs] fls] xs].
  cbn [snd fst] in *. auto.
Qed.

(** ** Work accounting

    [executions] counts actual executor invocations.  The law is
    unconditional: the merge runs each non-rejected transaction once, plus
    once more per conflict, whatever the speculation vector's length; a
    missing speculation is one unspeculated execution and no conflict. *)

Definition is_rejected (r : rcpt) : bool :=
  match fst (fst (fst (fst r))) with
  | SRejected => true
  | _ => false
  end.

Definition nonrejected (rs : list rcpt) : nat :=
  length (filter (fun r => negb (is_rejected r)) rs).

Lemma nonrejected_le : forall rs, nonrejected rs <= length rs.
Proof.
  intros rs. unfold nonrejected.
  induction rs as [| r rs' IH]; cbn; [lia |].
  destruct (negb (is_rejected r)); cbn; lia.
Qed.

Lemma finish_not_rejected :
  forall st bk nm fee g p o,
    is_rejected (snd (finish st bk nm fee g p o)) = false.
Proof.
  intros. unfold finish. destruct (o_ok o); reflexivity.
Qed.

Lemma step_gate_finish :
  forall st bk nm fee non t g p,
    gateb bk nm (fee, non, t, g, p) = true ->
    step (st, bk, nm) (fee, non, t, g, p)
    = finish st bk nm fee g p
             (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                   (of_nonces nm)).
Proof.
  intros st bk nm fee non t g p Hg. unfold step. rewrite Hg. reflexivity.
Qed.

Lemma step_not_rejected :
  forall st bk nm i,
    gateb bk nm i = true ->
    is_rejected (snd (step (st, bk, nm) i)) = false.
Proof.
  intros st bk nm [[[[fee non] t] g] p] Hg.
  rewrite step_gate_finish by exact Hg.
  apply finish_not_rejected.
Qed.

Theorem executions_law :
  forall ts specs m,
    executions m ts specs
    = nonrejected (snd (fst (omerge m ts specs))) + snd (omerge m ts specs).
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - reflexivity.
  - unfold executions, omerge in *. cbn [omergeX].
    destruct m as [[st bk] nm].
    unfold mstep, cstep.
    destruct (gateb bk nm i) eqn:Hgate.
    + destruct (hd_error specs) as [sp |] eqn:Hhd; cbn [option_map].
      * destruct (vcheck st bk nm (spec_out i sp)) eqn:Hv.
        -- destruct i as [[[[fee non] t] g] p].
           pose proof (finish_not_rejected st bk nm fee g p
                         (spec_out (fee, non, t, g, p) sp)) as Hf.
           destruct (finish st bk nm fee g p
                       (spec_out (fee, non, t, g, p) sp)) as [m1 r].
           cbn [snd] in Hf.
           specialize (IH (tl specs) m1).
           destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
           cbn [fst snd] in *.
           unfold nonrejected in *. cbn [filter]. rewrite Hf.
           cbn [negb length count_true]. lia.
        -- pose proof (step_not_rejected st bk nm i Hgate) as Hf.
           destruct (step (st, bk, nm) i) as [m1 r].
           cbn [snd] in Hf.
           specialize (IH (tl specs) m1).
           destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
           cbn [fst snd] in *.
           unfold nonrejected in *. cbn [filter]. rewrite Hf.
           cbn [negb length count_true]. lia.
      * pose proof (step_not_rejected st bk nm i Hgate) as Hf.
        destruct (step (st, bk, nm) i) as [m1 r].
        cbn [snd] in Hf.
        specialize (IH (tl specs) m1).
        destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
        cbn [fst snd] in *.
        unfold nonrejected in *. cbn [filter]. rewrite Hf.
        cbn [negb length count_true]. lia.
    + specialize (IH (tl specs) (st, bk, nm)).
      destruct (omergeX (st, bk, nm) rest (tl specs)) as [[[m2 rs] fls] xs].
      cbn [fst snd] in *.
      unfold nonrejected in *. unfold rejrcpt.
      cbn [filter is_rejected fst negb count_true length].
      lia.
Qed.

Lemma mstep_execs_le :
  forall m i os, snd (mstep m i os) <= 2.
Proof.
  intros [[st bk] nm] i os.
  unfold mstep.
  destruct (cstep (st, bk, nm) i (option_map (spec_out i) os)) as [mr fl].
  cbn [snd].
  destruct (gateb bk nm i); [destruct os; [destruct fl; lia | lia] | lia].
Qed.

Theorem work_upper :
  forall ts specs m, executions m ts specs <= 2 * length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. lia.
  - unfold executions in *. cbn [omergeX].
    pose proof (mstep_execs_le m i (hd_error specs)) as Hx.
    destruct (mstep m i (hd_error specs)) as [[[m1 r] fl] x].
    cbn [snd] in Hx.
    specialize (IH (tl specs) m1).
    destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
    cbn [snd length] in *. lia.
Qed.

Lemma mstep_execs_lower :
  forall m i os,
    (if negb (is_rejected (snd (fst (fst (mstep m i os))))) then 1 else 0)
    <= snd (mstep m i os).
Proof.
  intros [[st bk] nm] i os.
  unfold mstep.
  destruct (cstep (st, bk, nm) i (option_map (spec_out i) os))
    as [[m1 r] fl] eqn:EC.
  cbn [fst snd].
  destruct (gateb bk nm i) eqn:Hgate.
  - destruct (negb (is_rejected r)); destruct os; try (destruct fl); lia.
  - unfold cstep in EC. rewrite Hgate in EC.
    injection EC as E1 E2 E3. subst.
    cbn. lia.
Qed.

Theorem work_lower :
  forall ts specs m,
    nonrejected (snd (fst (omerge m ts specs))) <= executions m ts specs.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. unfold nonrejected. cbn. lia.
  - unfold executions, omerge in *. cbn [omergeX].
    pose proof (mstep_execs_lower m i (hd_error specs)) as Hx.
    destruct (mstep m i (hd_error specs)) as [[[m1 r] fl] x].
    cbn [fst snd] in Hx.
    specialize (IH (tl specs) m1).
    destruct (omergeX m1 rest (tl specs)) as [[[m2 rs] fls] xs].
    cbn [fst snd] in *.
    unfold nonrejected in *. cbn [filter].
    destruct (negb (is_rejected r)); cbn [length count_true]; lia.
Qed.

(** ** Fuel is never the binding constraint

    With every operation cost at least one, any fuel strictly above the
    gas budget produces the same run, so invoking [runp] with fuel equal
    to the gas limit loses nothing on an admitted transaction, whose limit
    covers the intrinsic cost. *)

Definition unit_costs : Prop :=
  1 <= c_sset C /\ 1 <= c_sreset C /\ 1 <= c_read C /\ 1 <= c_bal C
  /\ 1 <= c_nonce C /\ 1 <= c_while C /\ 1 <= c_emit C /\ 1 <= c_pay C
  /\ 1 <= c_call C /\ 1 <= c_base C.

Lemma wcost_ge1 :
  unit_costs -> forall cv v cd, 1 <= wcost cv v cd.
Proof.
  intros Hu cv v cd. unfold wcost.
  destruct Hu as (H1 & H2 & _).
  destruct (cv =? 0); [destruct (v =? 0) |]; lia.
Qed.

Theorem runp_fuel_ext :
  forall gas f1 f2 cur t rd brd nrd n bn nn w cred deb acc aacc,
    unit_costs -> gas < f1 -> gas < f2 ->
    runp f1 gas cur t rd brd nrd n bn nn w cred deb acc aacc
    = runp f2 gas cur t rd brd nrd n bn nn w cred deb acc aacc.
Proof.
  induction gas as [gas IH] using lt_wf_ind;
    intros f1 f2 cur t rd brd nrd n bn nn w cred deb acc aacc Hu H1 H2.
  destruct f1 as [| f1]; [lia |]. destruct f2 as [| f2]; [lia |].
  destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                 | d amt k | c arg amt k];
    try reflexivity; simpl.
  - (* TWrite *)
    destruct (wlookup w (cur, a)) as [cv |] eqn:Hw.
    + destruct (wcost cv v (kcold (cur, a) acc) <=? gas) eqn:Hg;
        [| reflexivity].
      pose proof (wcost_ge1 Hu cv v (kcold (cur, a) acc)) as Hc1.
      apply Nat.leb_le in Hg.
      rewrite (IH (gas - wcost cv v (kcold (cur, a) acc)) ltac:(lia) f1 f2
                  cur k rd brd nrd n bn nn (((cur, a), v) :: w) cred deb
                  ((cur, a) :: acc) aacc Hu ltac:(lia) ltac:(lia)).
      reflexivity.
    + destruct (wcost (rd n (cur, a)) v (kcold (cur, a) acc) <=? gas) eqn:Hg;
        [| reflexivity].
      pose proof (wcost_ge1 Hu (rd n (cur, a)) v (kcold (cur, a) acc)) as Hc1.
      apply Nat.leb_le in Hg.
      rewrite (IH (gas - wcost (rd n (cur, a)) v (kcold (cur, a) acc))
                  ltac:(lia) f1 f2 cur k rd brd nrd (S n) bn nn
                  (((cur, a), v) :: w) cred deb ((cur, a) :: acc) aacc
                  Hu ltac:(lia) ltac:(lia)).
      reflexivity.
  - (* TRead *)
    destruct (c_read C + kcold (cur, a) acc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_read C + kcold (cur, a) acc)
      by (destruct Hu as (_ & _ & Hr & _); lia).
    apply Nat.leb_le in Hg.
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + apply (IH (gas - (c_read C + kcold (cur, a) acc)) ltac:(lia) f1 f2
               cur (k v0) rd brd nrd n bn nn w cred deb ((cur, a) :: acc)
               aacc Hu ltac:(lia) ltac:(lia)).
    + rewrite (IH (gas - (c_read C + kcold (cur, a) acc)) ltac:(lia) f1 f2
                  cur (k (rd n (cur, a))) rd brd nrd (S n) bn nn w cred deb
                  ((cur, a) :: acc) aacc Hu ltac:(lia) ltac:(lia)).
      reflexivity.
  - (* TBal *)
    destruct (c_bal C + acold a aacc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_bal C + acold a aacc)
      by (destruct Hu as (_ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    rewrite (IH (gas - (c_bal C + acold a aacc)) ltac:(lia) f1 f2 cur
                (k (brd bn a + cred a - deb a)) rd brd nrd n (S bn) nn w
                cred deb acc (a :: aacc) Hu ltac:(lia) ltac:(lia)).
    reflexivity.
  - (* TNonce *)
    destruct (c_nonce C + acold a aacc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_nonce C + acold a aacc)
      by (destruct Hu as (_ & _ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    rewrite (IH (gas - (c_nonce C + acold a aacc)) ltac:(lia) f1 f2 cur
                (k (nrd nn a)) rd brd nrd n bn (S nn) w cred deb acc
                (a :: aacc) Hu ltac:(lia) ltac:(lia)).
    reflexivity.
  - (* TWhile *)
    destruct (c_while C + kcold (cur, a) acc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_while C + kcold (cur, a) acc)
      by (destruct Hu as (_ & _ & _ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + destruct (tst v0) eqn:Hz.
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) ltac:(lia) f1 f2
                  cur (tseq tb (TWhile a tst tb k)) rd brd nrd n bn nn w
                  cred deb ((cur, a) :: acc) aacc Hu ltac:(lia) ltac:(lia)).
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) ltac:(lia) f1 f2
                  cur k rd brd nrd n bn nn w cred deb ((cur, a) :: acc) aacc
                  Hu ltac:(lia) ltac:(lia)).
    + destruct (tst (rd n (cur, a))) eqn:Hz.
      * rewrite (IH (gas - (c_while C + kcold (cur, a) acc)) ltac:(lia) f1 f2
                    cur (tseq tb (TWhile a tst tb k)) rd brd nrd (S n) bn nn
                    w cred deb ((cur, a) :: acc) aacc
                    Hu ltac:(lia) ltac:(lia)).
        reflexivity.
      * rewrite (IH (gas - (c_while C + kcold (cur, a) acc)) ltac:(lia) f1 f2
                    cur k rd brd nrd (S n) bn nn w cred deb
                    ((cur, a) :: acc) aacc Hu ltac:(lia) ltac:(lia)).
        reflexivity.
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_emit C)
      by (destruct Hu as (_ & _ & _ & _ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    rewrite (IH (gas - c_emit C) ltac:(lia) f1 f2 cur k rd brd nrd n bn nn w
                cred deb acc aacc Hu ltac:(lia) ltac:(lia)).
    reflexivity.
  - (* TPay *)
    destruct (c_pay C + acold d aacc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_pay C + acold d aacc)
      by (destruct Hu as (_ & _ & _ & _ & _ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp.
    + rewrite (IH (gas - (c_pay C + acold d aacc)) ltac:(lia) f1 f2 cur
                  (k true) rd brd nrd n (S bn) nn w
                  (bupd cred d (cred d + amt)) (bupd deb cur (deb cur + amt))
                  acc (d :: aacc) Hu ltac:(lia) ltac:(lia)).
      reflexivity.
    + rewrite (IH (gas - (c_pay C + acold d aacc)) ltac:(lia) f1 f2 cur
                  (k false) rd brd nrd n (S bn) nn w cred deb acc (d :: aacc)
                  Hu ltac:(lia) ltac:(lia)).
      reflexivity.
  - (* TCall *)
    destruct (c_call C + acold c aacc <=? gas) eqn:Hg; [| reflexivity].
    assert (Hc1 : 1 <= c_call C + acold c aacc)
      by (destruct Hu as (_ & _ & _ & _ & _ & _ & _ & _ & Hx & _); lia).
    apply Nat.leb_le in Hg.
    destruct amt as [| amt'].
    + rewrite (IH (gas - (c_call C + acold c aacc)) ltac:(lia) f1 f2 c
                  (CODE c arg) rd brd nrd n bn nn w cred deb acc (c :: aacc)
                  Hu ltac:(lia) ltac:(lia)).
      pose proof (runp_gas_bound f2 (gas - (c_call C + acold c aacc)) c
                    (CODE c arg) rd brd nrd n bn nn w cred deb acc
                    (c :: aacc)) as Hgb.
      set (oc := runp f2 (gas - (c_call C + acold c aacc)) c (CODE c arg)
                      rd brd nrd n bn nn w cred deb acc (c :: aacc)) in *.
      destruct (o_ok oc) eqn:Hok.
      * rewrite (IH (o_gas oc) ltac:(lia) f1 f2 cur (k (Some (o_ret oc)))
                    rd brd nrd (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                    (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc)
                    Hu ltac:(lia) ltac:(lia)).
        reflexivity.
      * rewrite (IH (o_gas oc) ltac:(lia) f1 f2 cur (k None) rd brd nrd
                    (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc (c :: aacc)
                    Hu ltac:(lia) ltac:(lia)).
        reflexivity.
    + destruct (S amt' <=? brd bn cur + cred cur - deb cur) eqn:Hp.
      * rewrite (IH (gas - (c_call C + acold c aacc)) ltac:(lia) f1 f2 c
                    (CODE c arg) rd brd nrd n (S bn) nn w
                    (bupd cred c (cred c + S amt'))
                    (bupd deb cur (deb cur + S amt')) acc (c :: aacc)
                    Hu ltac:(lia) ltac:(lia)).
        pose proof (runp_gas_bound f2 (gas - (c_call C + acold c aacc)) c
                      (CODE c arg) rd brd nrd n (S bn) nn w
                      (bupd cred c (cred c + S amt'))
                      (bupd deb cur (deb cur + S amt')) acc (c :: aacc))
          as Hgb.
        set (oc := runp f2 (gas - (c_call C + acold c aacc)) c (CODE c arg)
                        rd brd nrd n (S bn) nn w
                        (bupd cred c (cred c + S amt'))
                        (bupd deb cur (deb cur + S amt'))
                        acc (c :: aacc)) in *.
        destruct (o_ok oc) eqn:Hok.
        -- rewrite (IH (o_gas oc) ltac:(lia) f1 f2 cur (k (Some (o_ret oc)))
                       rd brd nrd (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                       (o_cred oc) (o_deb oc) (o_acc oc) (o_aacc oc)
                       Hu ltac:(lia) ltac:(lia)).
           reflexivity.
        -- rewrite (IH (o_gas oc) ltac:(lia) f1 f2 cur (k None) rd brd nrd
                       (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc
                       (c :: aacc) Hu ltac:(lia) ltac:(lia)).
           reflexivity.
      * rewrite (IH (gas - (c_call C + acold c aacc)) ltac:(lia) f1 f2 cur
                    (k None) rd brd nrd n (S bn) nn w cred deb acc
                    (c :: aacc) Hu ltac:(lia) ltac:(lia)).
        reflexivity.
Qed.

Theorem fuel_not_binding :
  forall fee non t g p rd brd nrd f,
    unit_costs -> c_base C <= g -> g < f ->
    runp f (g - c_base C) fee t rd brd nrd 0 0 0 [] zerof
         (deb0 fee (g * (BF + p))) [] (aacc0 fee)
    = runt (fee, non, t, g, p) rd brd nrd.
Proof.
  intros fee non t g p rd brd nrd f Hu Hbase Hf.
  assert (Hb1 : 1 <= c_base C) by (destruct Hu as (_&_&_&_&_&_&_&_&_&Hx); lia).
  unfold runt. cbv beta iota zeta.
  apply runp_fuel_ext; [exact Hu | lia | lia].
Qed.

(** ** Instruction-level interleaving as read sources

    A per-read-instant semantics: each fall-through storage read observes
    the storage of an arbitrary machine sequence at that read's ordinal,
    and each balance and nonce read likewise.  Such an execution is by
    construction a run against the induced read sources, so the merge
    equals sequential execution under interleaving below transaction
    granularity as an instance of [optimistic_correct]. *)

Theorem interleaving_safe :
  forall ts m
         (stq : nat -> nat -> storage) (bkq : nat -> nat -> bank)
         (nmq : nat -> nat -> nonces),
    fst (omerge m ts
           (map (fun j =>
                   ((fun n k => stq j n k),
                    (fun n a => bkq j n a),
                    (fun n a => nmq j n a)) : spec)
                (seq 0 (length ts))))
    = seq_execr m ts.
Proof.
  intros. apply optimistic_correct.
Qed.

(** ** Gas soundness of the gate *)

Lemma gate_rejected :
  forall st bk nm i,
    gateb bk nm i = false ->
    step (st, bk, nm) i = ((st, bk, nm), rejrcpt).
Proof.
  intros st bk nm i Hg. unfold step. rewrite Hg. reflexivity.
Qed.

Lemma pauper_rejected :
  forall st bk nm fee non t g p,
    bk fee < g * (BF + p) ->
    step (st, bk, nm) (fee, non, t, g, p) = ((st, bk, nm), rejrcpt).
Proof.
  intros st bk nm fee non t g p Hlt. apply gate_rejected. unfold gateb.
  apply andb_false_iff. right. apply Nat.leb_gt. lia.
Qed.

Lemma nonce_mismatch_rejected :
  forall st bk nm fee non t g p,
    non <> nm fee ->
    step (st, bk, nm) (fee, non, t, g, p) = ((st, bk, nm), rejrcpt).
Proof.
  intros st bk nm fee non t g p Hne. apply gate_rejected. unfold gateb.
  apply andb_false_iff. left. apply andb_false_iff. right.
  apply Nat.eqb_neq. exact Hne.
Qed.

Lemma underbase_rejected :
  forall st bk nm fee non t g p,
    g < c_base C ->
    step (st, bk, nm) (fee, non, t, g, p) = ((st, bk, nm), rejrcpt).
Proof.
  intros st bk nm fee non t g p Hlt. apply gate_rejected. unfold gateb.
  apply andb_false_iff. left. apply andb_false_iff. left.
  apply Nat.leb_gt. exact Hlt.
Qed.

(** ** The operational dispatch scheduler *)

Fixpoint dgo (ts0 : list item) (m : mach) (ord : list nat)
             (seen : list (nat * mach)) : list (nat * mach) :=
  match ord with
  | [] => seen
  | p :: ps =>
      if existsb (fun pr => Nat.eqb (fst pr) p) seen
      then dgo ts0 m ps seen
      else
        match nth_error ts0 p with
        | None => dgo ts0 m ps seen
        | Some i => dgo ts0 (fst (step m i)) ps ((p, m) :: seen)
        end
  end.

Definition dispatch (m0 : mach) (ts : list item) (order : list nat)
  : list spec :=
  let seen := dgo ts m0 order [] in
  map (fun j =>
         match find (fun pr => Nat.eqb (fst pr) j) seen with
         | Some pr => spec_of (snd pr)
         | None => spec_of m0
         end)
      (seq 0 (length ts)).

Theorem scheduler_correct :
  forall ts order m,
    fst (omerge m ts (dispatch m ts order)) = seq_execr m ts.
Proof.
  intros ts order m. apply optimistic_correct.
Qed.

(** ** The in-order scheduler is perfect *)

Definition ditem : item := (0, 0, TDone, 0, 0).

Fixpoint mach_at (m : mach) (l : list item) (j : nat) {struct j} : mach :=
  match j, l with
  | 0, _ => m
  | S _, [] => m
  | S j', i :: r => mach_at (fst (step m i)) r j'
  end.

Fixpoint snaps (d : nat) (m : mach) (l : list item) : list (nat * mach) :=
  match l with
  | [] => []
  | i :: r => (d, m) :: snaps (S d) (fst (step m i)) r
  end.

Lemma snaps_keys :
  forall l d m, map fst (snaps d m l) = seq d (length l).
Proof.
  induction l as [| i r IH]; intros d m; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma snaps_In :
  forall l d m j,
    j < length l ->
    In (d + j, mach_at m l j) (snaps d m l).
Proof.
  induction l as [| i r IH]; intros d m j Hj; simpl in Hj; [lia |].
  destruct j; simpl.
  - left. rewrite Nat.add_0_r. reflexivity.
  - right. rewrite Nat.add_succ_r.
    apply (IH (S d) (fst (step m i)) j). lia.
Qed.

Lemma existsb_key_false :
  forall (seen : list (nat * mach)) (p : nat),
    ~ In p (map fst seen) ->
    existsb (fun pr => Nat.eqb (fst pr) p) seen = false.
Proof.
  induction seen as [| [q v] rest IH]; simpl; intros p Hn.
  - reflexivity.
  - destruct (Nat.eqb q p) eqn:He; simpl.
    + apply Nat.eqb_eq in He. subst. exfalso. apply Hn. left. reflexivity.
    + apply IH. intro Hin. apply Hn. right. exact Hin.
Qed.

Lemma find_key_unique :
  forall (l : list (nat * mach)) (j : nat) (v : mach),
    In (j, v) l ->
    NoDup (map fst l) ->
    find (fun pr => Nat.eqb (fst pr) j) l = Some (j, v).
Proof.
  induction l as [| [q u] rest IH]; simpl; intros j v Hin Hnd.
  - contradiction.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hq Hnd].
    destruct (Nat.eqb q j) eqn:He.
    + apply Nat.eqb_eq in He. subst q.
      destruct Hin as [Hin | Hin].
      * inversion Hin. reflexivity.
      * exfalso. apply Hq. apply (in_map fst) in Hin. exact Hin.
    + destruct Hin as [Hin | Hin].
      * injection Hin as e1 e2. apply Nat.eqb_neq in He. congruence.
      * apply IH; assumption.
Qed.

Lemma prefix_specs_length :
  forall l m, length (prefix_specs m l) = length l.
Proof.
  induction l as [| i r IH]; intros m; simpl;
    [reflexivity | f_equal; apply IH].
Qed.

Lemma prefix_specs_nth :
  forall l m j d,
    j < length l ->
    nth j (prefix_specs m l) d = spec_of (mach_at m l j).
Proof.
  induction l as [| i r IH]; intros m j d Hj; simpl in Hj; [lia |].
  destruct j; simpl.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma dgo_inorder :
  forall (l ts0 : list item) (d : nat) (m : mach)
         (seen : list (nat * mach)),
    (forall j, d <= j -> ~ In j (map fst seen)) ->
    (forall j, nth_error ts0 (d + j) = nth_error l j) ->
    dgo ts0 m (seq d (length l)) seen = rev (snaps d m l) ++ seen.
Proof.
  induction l as [| i r IH]; intros ts0 d m seen Hfresh Hidx; simpl.
  - reflexivity.
  - rewrite existsb_key_false by (apply Hfresh; lia).
    assert (Hd : nth_error ts0 d = Some i).
    { specialize (Hidx 0). rewrite Nat.add_0_r in Hidx. exact Hidx. }
    rewrite Hd.
    rewrite IH.
    + rewrite <- app_assoc. reflexivity.
    + intros j Hj Hin. simpl in Hin. destruct Hin as [He | Hin].
      * lia.
      * apply (Hfresh j); [lia | exact Hin].
    + intros j. specialize (Hidx (S j)). simpl in Hidx.
      rewrite Nat.add_succ_r in Hidx. exact Hidx.
Qed.

Theorem dispatch_in_order :
  forall ts m,
    dispatch m ts (seq 0 (length ts)) = prefix_specs m ts.
Proof.
  intros ts m. unfold dispatch.
  rewrite (dgo_inorder ts ts 0 m []).
  - rewrite app_nil_r.
    set (F := fun j =>
                match find (fun pr => Nat.eqb (fst pr) j)
                           (rev (snaps 0 m ts)) with
                | Some pr => spec_of (snd pr)
                | None => spec_of m
                end).
    apply nth_ext with (d := F 0) (d' := spec_of m).
    + rewrite length_map, length_seq. symmetry. apply prefix_specs_length.
    + intros j Hj. rewrite length_map, length_seq in Hj.
      rewrite map_nth.
      rewrite seq_nth by exact Hj.
      rewrite Nat.add_0_l.
      unfold F.
      rewrite (find_key_unique (rev (snaps 0 m ts)) j (mach_at m ts j)).
      * cbn [snd]. symmetry. apply prefix_specs_nth. exact Hj.
      * rewrite <- in_rev.
        assert (H := snaps_In ts 0 m j Hj).
        rewrite Nat.add_0_l in H. exact H.
      * rewrite map_rev, snaps_keys. apply NoDup_rev, seq_NoDup.
  - intros j _ Hin. simpl in Hin. contradiction.
  - intros j. reflexivity.
Qed.

Corollary scheduler_in_order_optimal :
  forall ts m,
    omerge m ts (dispatch m ts (seq 0 (length ts)))
    = (seq_execr m ts, 0).
Proof.
  intros ts m. rewrite dispatch_in_order. apply fast_path.
Qed.

Theorem work_inorder :
  forall ts m,
    executions m ts (dispatch m ts (seq 0 (length ts)))
    = nonrejected (snd (seq_execr m ts)).
Proof.
  intros ts m.
  rewrite executions_law.
  rewrite dispatch_in_order, fast_path. cbn [fst snd]. lia.
Qed.

(** ** Complete dispatch orders never fall back to the base default *)

Lemma dgo_seen_mono :
  forall ord ts0 m seen x,
    In x (map fst seen) -> In x (map fst (dgo ts0 m ord seen)).
Proof.
  induction ord as [| p ps IH]; intros ts0 m seen x Hx; cbn.
  - exact Hx.
  - destruct (existsb (fun pr => Nat.eqb (fst pr) p) seen) eqn:He.
    + apply IH. exact Hx.
    + destruct (nth_error ts0 p) as [i |] eqn:Hn.
      * apply IH. cbn. right. exact Hx.
      * apply IH. exact Hx.
Qed.

Lemma dgo_covers :
  forall ord ts0 m seen j,
    In j ord -> j < length ts0 ->
    In j (map fst (dgo ts0 m ord seen)).
Proof.
  induction ord as [| p ps IH]; intros ts0 m seen j Hin Hj; cbn.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + destruct (existsb (fun pr => Nat.eqb (fst pr) j) seen) eqn:He.
      * apply dgo_seen_mono.
        apply existsb_exists in He. destruct He as [pr [Hpr Heq]].
        apply Nat.eqb_eq in Heq.
        apply in_map_iff. exists pr. auto.
      * destruct (nth_error ts0 j) as [i |] eqn:Hn.
        -- apply dgo_seen_mono. cbn. left. reflexivity.
        -- exfalso. apply nth_error_None in Hn. lia.
    + destruct (existsb (fun pr => Nat.eqb (fst pr) p) seen) eqn:He.
      * apply IH; assumption.
      * destruct (nth_error ts0 p) as [i |] eqn:Hn; [apply IH | apply IH];
          assumption.
Qed.

Lemma dgo_nodup :
  forall ord ts0 m seen,
    NoDup (map fst seen) -> NoDup (map fst (dgo ts0 m ord seen)).
Proof.
  induction ord as [| p ps IH]; intros ts0 m seen Hnd; cbn.
  - exact Hnd.
  - destruct (existsb (fun pr => Nat.eqb (fst pr) p) seen) eqn:He.
    + apply IH. exact Hnd.
    + destruct (nth_error ts0 p) as [i |] eqn:Hn.
      * apply IH. cbn. constructor; [| exact Hnd].
        intro Hx. apply in_map_iff in Hx.
        destruct Hx as [[q v] [Hq Hin]]. cbn in Hq. subst q.
        assert (Ht : existsb (fun pr => Nat.eqb (fst pr) p) seen = true).
        { apply existsb_exists. exists (p, v).
          split; [exact Hin | cbn; apply Nat.eqb_refl]. }
        congruence.
      * apply IH. exact Hnd.
Qed.

(** A permutation of the block indices dispatches every position, so the
    base-state default arm of [dispatch] is dead: every speculation comes
    from an actual dispatch-time snapshot. *)

Theorem dispatch_complete :
  forall m ts ord j d,
    Permutation ord (seq 0 (length ts)) ->
    j < length ts ->
    exists mj,
      find (fun pr => Nat.eqb (fst pr) j) (dgo ts m ord [])
      = Some (j, mj)
      /\ nth j (dispatch m ts ord) d = spec_of mj.
Proof.
  intros m ts ord j d Hperm Hj.
  assert (Hin : In j ord).
  { apply Permutation_in with (l := seq 0 (length ts)).
    - apply Permutation_sym. exact Hperm.
    - apply in_seq. lia. }
  assert (Hcov : In j (map fst (dgo ts m ord []))).
  { apply dgo_covers; assumption. }
  apply in_map_iff in Hcov. destruct Hcov as [[q mj] [Hq Hpr]].
  cbn in Hq. subst q.
  exists mj.
  assert (Hfind : find (fun pr => Nat.eqb (fst pr) j) (dgo ts m ord [])
                  = Some (j, mj)).
  { apply find_key_unique; [exact Hpr |].
    apply dgo_nodup. cbn. constructor. }
  split; [exact Hfind |].
  unfold dispatch.
  set (F := fun j0 =>
              match find (fun pr => Nat.eqb (fst pr) j0) (dgo ts m ord []) with
              | Some pr => spec_of (snd pr)
              | None => spec_of m
              end).
  rewrite nth_indep with (d' := F 0)
    by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth.
  rewrite seq_nth by exact Hj.
  rewrite Nat.add_0_l.
  unfold F. rewrite Hfind. reflexivity.
Qed.

(** ** Wavefront retry bound *)

Theorem retry_progress :
  forall ts r m sps',
    snd (omerge m ts (firstn r (prefix_specs m ts) ++ sps'))
    <= length ts - r.
Proof.
  induction ts as [| i rest IH]; intros r m sps'.
  - cbn. lia.
  - destruct r as [| r'].
    + cbn [firstn app].
      etransitivity; [apply reexec_bound | cbn [length]; lia].
    + destruct m as [[st bk] nm]. destruct i as [[[[fee non] t] g] p].
      unfold omerge in *.
      cbn [prefix_specs firstn app omergeX hd_error tl length].
      unfold mstep, cstep.
      cbn [option_map spec_out spec_of fst snd].
      destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
      * assert (Hv : vcheck st bk nm
                       (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                             (of_nonces nm)) = true).
        { unfold vcheck, runt. cbv beta iota zeta.
          rewrite valid_self_s, bvalid_self_b, nvalid_self_n. reflexivity. }
        rewrite Hv.
        assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                        = finish st bk nm fee g p
                            (runt (fee, non, t, g, p) (of_state st)
                                  (of_bank bk) (of_nonces nm))).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        destruct (finish st bk nm fee g p
                    (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                          (of_nonces nm))) as [m1 r].
        cbn [fst].
        specialize (IH r' m1 sps').
        destruct (omergeX m1 rest (firstn r' (prefix_specs m1 rest) ++ sps'))
          as [[[m2 rs] fls] xs].
        cbn [snd fst] in IH.
        cbn [snd fst count_true]. lia.
      * assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                        = ((st, bk, nm), rejrcpt)).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        cbn [fst].
        specialize (IH r' (st, bk, nm) sps').
        destruct (omergeX (st, bk, nm) rest
                    (firstn r' (prefix_specs (st, bk, nm) rest) ++ sps'))
          as [[[m2 rs] fls] xs].
        cbn [snd fst] in IH.
        cbn [snd fst count_true]. lia.
Qed.

Corollary retry_converges :
  forall ts m,
    snd (omerge m ts (prefix_specs m ts)) = 0.
Proof.
  intros ts m. rewrite fast_path. reflexivity.
Qed.

(** ** The retry loop as a proof object

    Round-indexed synchronous re-speculation: round zero speculates every
    position from the base machine; round [S k] gives position 0 the base
    machine and position [S j] the machine that round [k] produced for
    position [j], advanced by item [j].  [jmach_progress] is the per-pass
    progress lemma: after [k] rounds the first [k] positions speculate
    against their true prefix machines, so the agreeing prefix grows by at
    least one position per pass and [length ts] rounds converge. *)

Fixpoint jmach (k : nat) (m : mach) (ts : list item) (j : nat) : mach :=
  match k with
  | 0 => m
  | S k' => match j with
            | 0 => m
            | S j' => fst (step (jmach k' m ts j') (nth j' ts ditem))
            end
  end.

Definition jspecs (k : nat) (m : mach) (ts : list item) : list spec :=
  map (fun j => spec_of (jmach k m ts j)) (seq 0 (length ts)).

Lemma mach_at_S :
  forall ts m j,
    j < length ts ->
    mach_at m ts (S j) = fst (step (mach_at m ts j) (nth j ts ditem)).
Proof.
  induction ts as [| i r IH]; intros m j Hj; cbn in Hj; [lia |].
  destruct j; cbn [mach_at nth].
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma jmach_progress :
  forall k m ts j,
    j <= k -> j <= length ts ->
    jmach k m ts j = mach_at m ts j.
Proof.
  induction k as [| k' IH]; intros m ts j Hk Hlen.
  - assert (j = 0) by lia. subst. destruct ts; reflexivity.
  - destruct j as [| j'].
    + destruct ts; reflexivity.
    + cbn [jmach]. rewrite (IH m ts j') by lia.
      symmetry. apply mach_at_S. lia.
Qed.

Lemma jspecs_nth :
  forall k m ts j,
    j < length ts ->
    nth j (jspecs k m ts) (spec_of m) = spec_of (jmach k m ts j).
Proof.
  intros k m ts j Hj. unfold jspecs.
  rewrite nth_indep with (d' := spec_of (jmach k m ts 0))
    by (rewrite length_map, length_seq; exact Hj).
  change (spec_of (jmach k m ts 0))
    with ((fun j0 => spec_of (jmach k m ts j0)) 0).
  rewrite map_nth. rewrite seq_nth by exact Hj. reflexivity.
Qed.

Lemma firstn_nth_ext :
  forall (A : Type) (d : A) r (l1 l2 : list A),
    (forall j, j < r -> j < length l1 -> nth j l1 d = nth j l2 d) ->
    length l1 = length l2 ->
    firstn r l1 = firstn r l2.
Proof.
  intros A d r. induction r as [| r' IH]; intros l1 l2 Hj Hlen.
  - reflexivity.
  - destruct l1 as [| x1 l1']; destruct l2 as [| x2 l2'];
      cbn in Hlen; try lia.
    + reflexivity.
    + cbn [firstn]. f_equal.
      * apply (Hj 0); cbn; lia.
      * apply IH; [| lia].
        intros j Hjr Hjl. apply (Hj (S j)); cbn; lia.
Qed.

Lemma jspecs_agree :
  forall k m ts,
    firstn (Nat.min k (length ts)) (jspecs k m ts)
    = firstn (Nat.min k (length ts)) (prefix_specs m ts).
Proof.
  intros k m ts.
  apply (firstn_nth_ext spec (spec_of m)).
  - intros j Hjr Hjl.
    unfold jspecs in Hjl. rewrite length_map, length_seq in Hjl.
    rewrite jspecs_nth by exact Hjl.
    rewrite prefix_specs_nth by exact Hjl.
    rewrite jmach_progress by lia.
    reflexivity.
  - unfold jspecs. rewrite length_map, length_seq.
    symmetry. apply prefix_specs_length.
Qed.

Theorem retry_round_progress :
  forall ts m k,
    snd (omerge m ts (jspecs k m ts)) <= length ts - k.
Proof.
  intros ts m k.
  rewrite <- (firstn_skipn (Nat.min k (length ts)) (jspecs k m ts)).
  rewrite jspecs_agree.
  etransitivity; [apply retry_progress | lia].
Qed.

Theorem retry_loop_converges :
  forall ts m,
    snd (omerge m ts (jspecs (length ts) m ts)) = 0.
Proof.
  intros ts m.
  assert (H := retry_round_progress ts m (length ts)). lia.
Qed.

(** ** Retry total work

    The synchronous loop runs the merge once per round.  Total executor
    invocations across the [length ts] rounds convergence needs are
    bounded quadratically; the per-round flags are false strictly below
    the round index, so a selective scheduler that reruns only flagged
    positions performs at most [n - k] re-executions in round [k]. *)

Fixpoint sumf (f : nat -> nat) (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => sumf f k' + f k'
  end.

Lemma sumf_ext :
  forall f g k, (forall j, j < k -> f j = g j) -> sumf f k = sumf g k.
Proof.
  intros f g k H. induction k as [| k' IH]; cbn [sumf].
  - reflexivity.
  - rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumf_S :
  forall f n, sumf (fun k => S (f k)) n = sumf f n + n.
Proof.
  intros f n. induction n as [| n' IH]; cbn [sumf]; [reflexivity |].
  rewrite IH. lia.
Qed.

Lemma sumf_bound :
  forall (f B : nat -> nat) k,
    (forall j, j < k -> f j <= B j) ->
    sumf f k <= sumf B k.
Proof.
  intros f B k H. induction k as [| k' IH]; cbn [sumf]; [lia |].
  assert (f k' <= B k') by (apply H; lia).
  assert (sumf f k' <= sumf B k') by (apply IH; intros; apply H; lia).
  lia.
Qed.

Lemma sumf_sub : forall n, 2 * sumf (fun k => n - k) n = n * S n.
Proof.
  induction n as [| n' IH]; [reflexivity |].
  cbn [sumf].
  rewrite (sumf_ext (fun k => S n' - k) (fun k => S (n' - k)) n')
    by (intros j Hj; lia).
  rewrite sumf_S.
  replace (S n' - n') with 1 by lia.
  set (X := sumf (fun k => n' - k) n') in *.
  nia.
Qed.

Lemma sumf_linear :
  forall n k,
    sumf (fun k0 => n + (n - k0)) k = k * n + sumf (fun k0 => n - k0) k.
Proof.
  intros n k. induction k as [| k' IH]; cbn [sumf]; [lia | rewrite IH; lia].
Qed.

Lemma round_execs_bound :
  forall ts m k,
    executions m ts (jspecs k m ts) <= length ts + (length ts - k).
Proof.
  intros ts m k.
  rewrite executions_law.
  pose proof (retry_round_progress ts m k) as Hc.
  pose proof (omergeX_len ts (jspecs k m ts) m) as [Hlr _].
  pose proof (nonrejected_le (snd (fst (fst (omergeX m ts (jspecs k m ts))))))
    as Hnr.
  unfold omerge in *.
  destruct (omergeX m ts (jspecs k m ts)) as [[[m2 rs] fls] xs].
  cbn [fst snd] in *.
  lia.
Qed.

Definition retry_execs (m : mach) (ts : list item) : nat :=
  sumf (fun k => executions m ts (jspecs k m ts)) (length ts).

Theorem retry_work_bound :
  forall ts m,
    2 * retry_execs m ts <= 3 * length ts * length ts + length ts.
Proof.
  intros ts m. unfold retry_execs.
  assert (Hb : sumf (fun k => executions m ts (jspecs k m ts)) (length ts)
               <= sumf (fun k => length ts + (length ts - k)) (length ts)).
  { apply sumf_bound. intros j Hj. apply round_execs_bound. }
  rewrite sumf_linear in Hb.
  pose proof (sumf_sub (length ts)) as Hs.
  nia.
Qed.

Lemma flags_prefix_false :
  forall ts r m sps' j,
    j < r -> j < length ts ->
    nth j (reexec_flags m ts (firstn r (prefix_specs m ts) ++ sps')) true
    = false.
Proof.
  induction ts as [| i rest IH]; intros r m sps' j Hjr Hjl;
    [cbn in Hjl; lia |].
  destruct r as [| r']; [lia |].
  destruct m as [[st bk] nm]. destruct i as [[[[fee non] t] g] p].
  unfold reexec_flags in *.
  cbn [prefix_specs firstn app omergeX hd_error tl].
  unfold mstep, cstep.
  cbn [option_map spec_out spec_of fst snd].
  destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
  - assert (Hv : vcheck st bk nm
                   (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                         (of_nonces nm)) = true).
    { unfold vcheck, runt. cbv beta iota zeta.
      rewrite valid_self_s, bvalid_self_b, nvalid_self_n. reflexivity. }
    rewrite Hv.
    assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                    = finish st bk nm fee g p
                        (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                              (of_nonces nm))).
    { unfold step. rewrite Hgate. reflexivity. }
    rewrite Hstep.
    destruct (finish st bk nm fee g p
                (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                      (of_nonces nm))) as [m1 r].
    cbn [fst].
    destruct (omergeX m1 rest (firstn r' (prefix_specs m1 rest) ++ sps'))
      as [[[m2 rs] fls] xs] eqn:EX.
    cbn [snd fst].
    destruct j as [| j']; cbn [nth]; [reflexivity |].
    cbn [length] in Hjl.
    pose proof (IH r' m1 sps' j' ltac:(lia) ltac:(lia)) as HI.
    unfold reexec_flags in HI. rewrite EX in HI. cbn [snd fst] in HI.
    exact HI.
  - assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                    = ((st, bk, nm), rejrcpt)).
    { unfold step. rewrite Hgate. reflexivity. }
    rewrite Hstep.
    cbn [fst].
    destruct (omergeX (st, bk, nm) rest
                (firstn r' (prefix_specs (st, bk, nm) rest) ++ sps'))
      as [[[m2 rs] fls] xs] eqn:EX.
    cbn [snd fst].
    destruct j as [| j']; cbn [nth]; [reflexivity |].
    cbn [length] in Hjl.
    pose proof (IH r' (st, bk, nm) sps' j' ltac:(lia) ltac:(lia)) as HI.
    unfold reexec_flags in HI. rewrite EX in HI. cbn [snd fst] in HI.
    exact HI.
Qed.

Theorem retry_flags :
  forall ts m k j,
    j < k -> j < length ts ->
    nth j (reexec_flags m ts (jspecs k m ts)) true = false.
Proof.
  intros ts m k j Hjk Hjl.
  rewrite <- (firstn_skipn (Nat.min k (length ts)) (jspecs k m ts)).
  rewrite jspecs_agree.
  apply flags_prefix_false; [lia | exact Hjl].
Qed.

Theorem selective_retry_bound :
  forall ts m k,
    snd (omerge m ts (jspecs k m ts)) <= length ts - k
    /\ (forall j, j < k -> j < length ts ->
          nth j (reexec_flags m ts (jspecs k m ts)) true = false).
Proof.
  intros ts m k.
  split; [apply retry_round_progress |].
  intros j Hjk Hjl. apply retry_flags; assumption.
Qed.

(** ** Money conservation

    The bank is an exact ledger across gas, coinbase, burn, and transfers:
    for every account, final balance plus debits equals initial balance
    plus credits.  Debits are the effective gas paid at the full price,
    base fee plus tip, by transactions the account sponsored plus the
    transfers it sent, from any frame; credits are coinbase tip income
    plus transfers received.  The burned base fee appears in no account's
    credits, which the supply theorem below makes global. *)

Fixpoint debits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (fee, _, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb fee f then u * (BF + p) else 0) + outsum f tvs
      + debits f ts' rs'
  | _, _ => 0
  end.

Fixpoint credits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (_, _, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb CB f then u * p else 0) + insum f tvs + credits f ts' rs'
  | _, _ => 0
  end.

(** The bank algebra of a committing transaction: upfront hold at the
    effective price, transfer settlement, refund of the unconsumed and
    refunded portion, coinbase tip, burned base fee.  Stated raw so the
    ledger proofs can cite it pointwise. *)

Lemma commit_bank_law :
  forall (bk : bank) fee g p (tvs : list transfer) ue f,
    g * (BF + p) <= bk fee ->
    ue <= g ->
    apply_ok (bupd bk fee (bk fee - g * (BF + p))) tvs = true ->
    bupd (bupd (apply_tvs (bupd bk fee (bk fee - g * (BF + p))) tvs) fee
               (apply_tvs (bupd bk fee (bk fee - g * (BF + p))) tvs fee
                + (g - ue) * (BF + p))) CB
         (bupd (apply_tvs (bupd bk fee (bk fee - g * (BF + p))) tvs) fee
               (apply_tvs (bupd bk fee (bk fee - g * (BF + p))) tvs fee
                + (g - ue) * (BF + p)) CB + ue * p) f
    + (if Nat.eqb fee f then ue * (BF + p) else 0) + outsum f tvs
    = bk f + (if Nat.eqb CB f then ue * p else 0) + insum f tvs.
Proof.
  intros bk fee g p tvs ue f Hgle Hue Hok.
  assert (AL := apply_law tvs (bupd bk fee (bk fee - g * (BF + p))) Hok f).
  assert (Huep : ue * (BF + p) <= g * (BF + p))
    by (apply Nat.mul_le_mono_r; lia).
  assert (Hdist : (g - ue) * (BF + p) = g * (BF + p) - ue * (BF + p))
    by (apply Nat.mul_sub_distr_r).
  set (b2 := apply_tvs (bupd bk fee (bk fee - g * (BF + p))) tvs) in *.
  unfold bupd. unfold bupd in AL.
  destruct (Nat.eqb fee f) eqn:Hff;
    destruct (Nat.eqb CB f) eqn:Hcb;
    destruct (Nat.eqb f fee) eqn:Hff';
    destruct (Nat.eqb f CB) eqn:Hcb';
    destruct (Nat.eqb CB fee) eqn:Hcf;
    repeat match goal with
           | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
           | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
           end;
    try congruence; subst; lia.
Qed.

Lemma revert_bank_law :
  forall (bk : bank) fee g p u f,
    g * (BF + p) <= bk fee ->
    u <= g ->
    bupd (bupd bk fee (bk fee - u * (BF + p))) CB
         (bupd bk fee (bk fee - u * (BF + p)) CB + u * p) f
    + (if Nat.eqb fee f then u * (BF + p) else 0)
    = bk f + (if Nat.eqb CB f then u * p else 0).
Proof.
  intros bk fee g p u f Hgle Hu.
  assert (Hup : u * (BF + p) <= g * (BF + p))
    by (apply Nat.mul_le_mono_r; lia).
  unfold bupd.
  destruct (Nat.eqb fee f) eqn:Hff;
    destruct (Nat.eqb CB f) eqn:Hcb;
    destruct (Nat.eqb f fee) eqn:Hff';
    destruct (Nat.eqb f CB) eqn:Hcb';
    destruct (Nat.eqb CB fee) eqn:Hcf;
    repeat match goal with
           | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
           | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
           end;
    try congruence; subst; lia.
Qed.

Lemma gate_funds :
  forall bk nm fee non t g p,
    gateb bk nm (fee, non, t, g, p) = true ->
    g * (BF + p) <= bk fee.
Proof.
  intros bk nm fee non t g p Hg.
  unfold gateb in Hg.
  apply andb_true_iff in Hg. destruct Hg as [_ Hg3].
  apply Nat.leb_le. exact Hg3.
Qed.

Theorem money_conservation :
  forall ts m f,
    snd (fst (fst (seq_execr m ts))) f + debits f ts (snd (seq_execr m ts))
    = snd (fst m) f + credits f ts (snd (seq_execr m ts)).
Proof.
  induction ts as [| i rest IH]; intros m f.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[[fee non] t] g] p].
    cbn [seq_execr].
    destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
    + assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = finish st bk nm fee g p
                          (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      set (o := runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                     (of_nonces nm)) in *.
      assert (Hgle : g * (BF + p) <= bk fee)
        by (apply (gate_funds bk nm fee non t g p Hgate)).
      unfold finish. cbv zeta.
      destruct (o_ok o) eqn:Hok; cbv beta iota.
      * set (u := g - o_gas o) in *.
        set (ue := u - Nat.min (o_ref o) (u / 2)) in *.
        assert (Hbag : forall a v, In (a, v) (o_blog o) -> bk a = v).
        { apply bvalid_true_In. unfold o, runt. cbv beta iota zeta.
          apply bvalid_self_b. }
        assert (Hinv0 : inflight_inv bk
                          (bupd bk fee (bk fee - g * (BF + p)))
                          zerof (deb0 fee (g * (BF + p)))).
        { intros a. unfold bupd, deb0, zerof.
          destruct (Nat.eqb a fee) eqn:Haf.
          - apply Nat.eqb_eq in Haf. subst a. lia.
          - lia. }
        assert (HIS := inflight_sound g (g - c_base C) fee t (of_state st)
                         (of_bank bk) (of_nonces nm) 0 0 0 [] zerof
                         (deb0 fee (g * (BF + p))) [] (aacc0 fee)
                         bk (bupd bk fee (bk fee - g * (BF + p)))
                         Hbag Hinv0).
        assert (Hokb : apply_ok (bupd bk fee (bk fee - g * (BF + p)))
                         (o_tvs o) = true)
          by (exact (proj1 HIS)).
        assert (Hue : ue <= g)
          by (eapply Nat.le_trans; apply Nat.le_sub_l).
        assert (Hsb := commit_bank_law bk fee g p (o_tvs o) ue f
                         Hgle Hue Hokb).
        match goal with
        | |- context [seq_execr ?M rest] =>
            destruct (seq_execr M rest) as [m2 rs] eqn:E2;
            assert (HI := IH M f)
        end.
        rewrite E2 in HI. cbn [fst snd] in HI.
        cbn [fst snd debits credits].
        lia.
      * set (u := g - o_gas o) in *.
        assert (Hu : u <= g) by (apply Nat.le_sub_l).
        assert (Hsb := revert_bank_law bk fee g p u f Hgle Hu).
        match goal with
        | |- context [seq_execr ?M rest] =>
            destruct (seq_execr M rest) as [m2 rs] eqn:E2;
            assert (HI := IH M f)
        end.
        rewrite E2 in HI. cbn [fst snd] in HI.
        cbn [fst snd debits credits outsum insum].
        lia.
    + assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = ((st, bk, nm), rejrcpt)).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
      unfold rejrcpt.
      cbn [fst snd debits credits outsum insum].
      destruct (Nat.eqb fee f); destruct (Nat.eqb CB f); cbn; lia.
Qed.

Corollary omerge_money_conservation :
  forall ts specs m f,
    snd (fst (fst (fst (omerge m ts specs)))) f
    + debits f ts (snd (fst (omerge m ts specs)))
    = snd (fst m) f + credits f ts (snd (fst (omerge m ts specs))).
Proof.
  intros ts specs m f.
  rewrite (optimistic_correct ts specs m).
  apply money_conservation.
Qed.

(** ** Nonce ledger

    An account's nonce advances by exactly the number of non-rejected
    transactions it sponsored. *)

Fixpoint execd (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (fee, _, _, _, _) :: ts', (stt, _, _, _, _) :: rs' =>
      (if Nat.eqb fee f
       then match stt with SRejected => 0 | _ => 1 end
       else 0) + execd f ts' rs'
  | _, _ => 0
  end.

Theorem nonce_law :
  forall ts m f,
    snd (fst (seq_execr m ts)) f
    = snd m f + execd f ts (snd (seq_execr m ts)).
Proof.
  induction ts as [| i rest IH]; intros m f.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[[fee non] t] g] p].
    cbn [seq_execr].
    destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hgate.
    + assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = finish st bk nm fee g p
                          (runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      set (o := runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                     (of_nonces nm)) in *.
      unfold finish. cbv zeta.
      assert (Hnm : forall f0,
                 bupd nm fee (S (nm fee)) f0
                 = nm f0 + (if Nat.eqb fee f0 then 1 else 0)).
      { intros f0. unfold bupd.
        destruct (Nat.eqb f0 fee) eqn:Hf0;
          destruct (Nat.eqb fee f0) eqn:Hf1;
          repeat match goal with
                 | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
                 | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
                 end;
          try congruence; lia. }
      destruct (o_ok o) eqn:Hok; cbv beta iota.
      * match goal with
        | |- context [seq_execr ?M rest] =>
            destruct (seq_execr M rest) as [m2 rs] eqn:E2;
            assert (HI := IH M f)
        end.
        rewrite E2 in HI. cbn [fst snd] in HI.
        rewrite (Hnm f) in HI.
        cbn [fst snd execd].
        lia.
      * match goal with
        | |- context [seq_execr ?M rest] =>
            destruct (seq_execr M rest) as [m2 rs] eqn:E2;
            assert (HI := IH M f)
        end.
        rewrite E2 in HI. cbn [fst snd] in HI.
        rewrite (Hnm f) in HI.
        cbn [fst snd execd].
        lia.
    + assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                      = ((st, bk, nm), rejrcpt)).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
      unfold rejrcpt.
      cbn [fst snd execd].
      destruct (Nat.eqb fee f); cbn; lia.
Qed.

Lemma seq_rcpt_len :
  forall ts m, length (snd (seq_execr m ts)) = length ts.
Proof.
  induction ts as [| i rest IH]; intros m; cbn [seq_execr].
  - reflexivity.
  - destruct (step m i) as [m1 r].
    destruct (seq_execr m1 rest) as [m2 rs] eqn:E.
    assert (HI := IH m1). rewrite E in HI. cbn in HI |- *. lia.
Qed.

(** ** Abstract supply conservation

    Over any duplicate-free address list containing the coinbase, every
    sponsoring account, and every transfer party, the bank total decreases
    by exactly the burned base fee: the effective price splits into the
    coinbase tip, which stays in the sum, and the burned base portion,
    which leaves it.  No hypotheses on the machine. *)

Fixpoint asum (b : addr -> nat) (A : list addr) : nat :=
  match A with
  | [] => 0
  | a :: A' => b a + asum b A'
  end.

Lemma asum_ext :
  forall A (F G : addr -> nat),
    (forall a, F a = G a) -> asum F A = asum G A.
Proof.
  induction A as [| a A' IH]; intros F G H; cbn; [reflexivity |].
  rewrite (H a), (IH F G H). reflexivity.
Qed.

Lemma asum_plus :
  forall A (F G : addr -> nat),
    asum (fun a => F a + G a) A = asum F A + asum G A.
Proof.
  induction A as [| a A' IH]; intros F G; cbn; [reflexivity |].
  rewrite IH. lia.
Qed.

Lemma asum_zero : forall A, asum (fun _ => 0) A = 0.
Proof.
  induction A as [| a A' IH]; cbn; [reflexivity | exact IH].
Qed.

Lemma asum_delta_absent :
  forall A x v,
    ~ In x A ->
    asum (fun a => if Nat.eqb x a then v else 0) A = 0.
Proof.
  induction A as [| a A' IH]; intros x v Hnin; cbn; [reflexivity |].
  destruct (Nat.eqb x a) eqn:He.
  - apply Nat.eqb_eq in He. subst. exfalso. apply Hnin. left. reflexivity.
  - rewrite IH; [reflexivity |]. intro Hx. apply Hnin. right. exact Hx.
Qed.

Lemma asum_delta :
  forall A x v,
    NoDup A -> In x A ->
    asum (fun a => if Nat.eqb x a then v else 0) A = v.
Proof.
  induction A as [| a A' IH]; intros x v Hnd Hin; cbn; [contradiction |].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
  destruct Hin as [-> | Hin].
  - rewrite Nat.eqb_refl. rewrite asum_delta_absent by exact Ha. lia.
  - destruct (Nat.eqb x a) eqn:He.
    + apply Nat.eqb_eq in He. subst. contradiction.
    + rewrite (IH x v Hnd Hin). lia.
Qed.

Fixpoint tvtotal (l : list transfer) : nat :=
  match l with
  | [] => 0
  | (_, _, amt) :: r => amt + tvtotal r
  end.

Lemma asum_outsum :
  forall tvs A,
    NoDup A ->
    (forall s d amt, In (s, d, amt) tvs -> In s A) ->
    asum (fun f => outsum f tvs) A = tvtotal tvs.
Proof.
  induction tvs as [| [[s d] amt] r IH]; intros A Hnd Hsend.
  - rewrite (asum_ext A _ (fun _ => 0)) by reflexivity.
    apply asum_zero.
  - rewrite (asum_ext A (fun f => outsum f (((s, d, amt)) :: r))
               (fun f => (if Nat.eqb s f then amt else 0) + outsum f r))
      by reflexivity.
    rewrite asum_plus.
    rewrite (asum_delta A s amt Hnd
               (Hsend s d amt (or_introl eq_refl))).
    rewrite (IH A Hnd) by (intros s0 d0 a0 Hin; apply (Hsend s0 d0 a0);
                           right; exact Hin).
    cbn [tvtotal]. reflexivity.
Qed.

Lemma asum_insum :
  forall tvs A,
    NoDup A ->
    (forall s d amt, In (s, d, amt) tvs -> In d A) ->
    asum (fun f => insum f tvs) A = tvtotal tvs.
Proof.
  induction tvs as [| [[s d] amt] r IH]; intros A Hnd Hrecv.
  - rewrite (asum_ext A _ (fun _ => 0)) by reflexivity.
    apply asum_zero.
  - rewrite (asum_ext A (fun f => insum f (((s, d, amt)) :: r))
               (fun f => (if Nat.eqb d f then amt else 0) + insum f r))
      by reflexivity.
    rewrite asum_plus.
    rewrite (asum_delta A d amt Hnd
               (Hrecv s d amt (or_introl eq_refl))).
    rewrite (IH A Hnd) by (intros s0 d0 a0 Hin; apply (Hrecv s0 d0 a0);
                           right; exact Hin).
    cbn [tvtotal]. reflexivity.
Qed.

Fixpoint burned (rs : list rcpt) : nat :=
  match rs with
  | [] => 0
  | (_, u, _, _, _) :: rs' => u * BF + burned rs'
  end.

Fixpoint tx_parties (ts : list item) (rs : list rcpt) : list addr :=
  match ts, rs with
  | i :: ts', r :: rs' =>
      fst (fst (fst (fst i)))
        :: (let '(_, _, _, _, tvs) := r in
            map (fun tv => fst (fst tv)) tvs
            ++ map (fun tv => snd (fst tv)) tvs)
        ++ tx_parties ts' rs'
  | _, _ => []
  end.

Lemma asum_money :
  forall ts m A,
    asum (snd (fst (fst (seq_execr m ts)))) A
      + asum (fun f => debits f ts (snd (seq_execr m ts))) A
    = asum (snd (fst m)) A
      + asum (fun f => credits f ts (snd (seq_execr m ts))) A.
Proof.
  intros ts m A. induction A as [| a A' IH]; cbn [asum]; [lia |].
  pose proof (money_conservation ts m a). lia.
Qed.

Lemma asum_debits_nil :
  forall A, asum (fun f => debits f [] []) A = 0.
Proof.
  induction A as [| a A' IH]; cbn [asum debits]; [reflexivity |].
  rewrite asum_zero. reflexivity.
Qed.

Lemma asum_credits_nil :
  forall A, asum (fun f => credits f [] []) A = 0.
Proof.
  induction A as [| a A' IH]; cbn [asum credits]; [reflexivity |].
  rewrite asum_zero. reflexivity.
Qed.

Lemma asum_debits_cons :
  forall A fee non t g p ts' stt u w evs tvs rs',
    asum (fun f => debits f ((fee, non, t, g, p) :: ts')
                          ((stt, u, w, evs, tvs) :: rs')) A
    = asum (fun f => if Nat.eqb fee f then u * (BF + p) else 0) A
      + asum (fun f => outsum f tvs) A
      + asum (fun f => debits f ts' rs') A.
Proof.
  intros. induction A as [| a A' IH]; cbn [asum]; [reflexivity |].
  cbn [debits] in IH |- *. lia.
Qed.

Lemma asum_credits_cons :
  forall A fee non t g p ts' stt u w evs tvs rs',
    asum (fun f => credits f ((fee, non, t, g, p) :: ts')
                           ((stt, u, w, evs, tvs) :: rs')) A
    = asum (fun f => if Nat.eqb CB f then u * p else 0) A
      + asum (fun f => insum f tvs) A
      + asum (fun f => credits f ts' rs') A.
Proof.
  intros. induction A as [| a A' IH]; cbn [asum]; [reflexivity |].
  cbn [credits] in IH |- *. lia.
Qed.

Lemma debits_credits_burned :
  forall ts rs A,
    length rs = length ts ->
    NoDup A -> In CB A ->
    incl (tx_parties ts rs) A ->
    asum (fun f => debits f ts rs) A
    = asum (fun f => credits f ts rs) A + burned rs.
Proof.
  induction ts as [| i ts' IH]; intros rs A Hlen Hnd Hcb Hincl.
  - destruct rs as [| r rs']; cbn in Hlen; [| lia].
    rewrite asum_debits_nil, asum_credits_nil. reflexivity.
  - destruct rs as [| r rs']; cbn in Hlen; [lia |].
    destruct i as [[[[fee non] t] g] p].
    destruct r as [[[[stt u] w] evs] tvs].
    cbn [tx_parties fst] in Hincl.
    assert (Hfee : In fee A) by (apply Hincl; left; reflexivity).
    assert (Hsend : forall s d amt, In (s, d, amt) tvs -> In s A).
    { intros s d amt Hin. apply Hincl. right. apply in_or_app. left.
      apply in_or_app. left.
      apply in_map_iff. exists (s, d, amt). split; [reflexivity | exact Hin]. }
    assert (Hrecv : forall s d amt, In (s, d, amt) tvs -> In d A).
    { intros s d amt Hin. apply Hincl. right. apply in_or_app. left.
      apply in_or_app. right.
      apply in_map_iff. exists (s, d, amt). split; [reflexivity | exact Hin]. }
    assert (Hincl' : incl (tx_parties ts' rs') A).
    { intros a Ha. apply Hincl. right. apply in_or_app. right. exact Ha. }
    rewrite asum_debits_cons, asum_credits_cons.
    rewrite (asum_delta A fee (u * (BF + p)) Hnd Hfee).
    rewrite (asum_outsum tvs A Hnd Hsend).
    rewrite (asum_delta A CB (u * p) Hnd Hcb).
    rewrite (asum_insum tvs A Hnd Hrecv).
    rewrite (IH rs' A ltac:(lia) Hnd Hcb Hincl').
    cbn [burned].
    assert (Hd : u * (BF + p) = u * BF + u * p)
      by (apply Nat.mul_add_distr_l).
    lia.
Qed.

Theorem supply_conservation_abstract :
  forall ts m A,
    NoDup A -> In CB A ->
    incl (tx_parties ts (snd (seq_execr m ts))) A ->
    asum (snd (fst (fst (seq_execr m ts)))) A + burned (snd (seq_execr m ts))
    = asum (snd (fst m)) A.
Proof.
  intros ts m A Hnd Hcb Hincl.
  pose proof (asum_money ts m A) as Hm.
  pose proof (debits_credits_burned ts (snd (seq_execr m ts)) A
                (seq_rcpt_len ts m) Hnd Hcb Hincl) as Hd.
  lia.
Qed.

(** ** Static footprints

    [fp Fr Fw Br Bw Nr cok cur t] certifies, on the syntax of [t] running
    as [cur], that every storage read (including the transition read a
    write performs) lands in [Fr], every write in [Fw], every balance read
    (including the point-of-pay and value-call reads of the payer) in
    [Br], every transfer party in [Bw], and every nonce read in [Nr].
    Calls are certified through [cok], a set of contracts whose code is
    itself certified under the same footprints by [code_certified]; a
    zero-value call needs no balance footprint.  Conflict freedom becomes
    checkable without computing the runs it constrains. *)

Fixpoint fp (Fr Fw : list key) (Br Bw Nr : list addr) (cok : addr -> Prop)
         (cur : addr) (t : tx) : Prop :=
  match t with
  | TDone => True
  | TRet _ => True
  | TRevert => True
  | TWrite a v k =>
      In (cur, a) Fw /\ In (cur, a) Fr /\ fp Fr Fw Br Bw Nr cok cur k
  | TRead a k =>
      In (cur, a) Fr /\ forall v, fp Fr Fw Br Bw Nr cok cur (k v)
  | TBal a k =>
      In a Br /\ forall v, fp Fr Fw Br Bw Nr cok cur (k v)
  | TNonce a k =>
      In a Nr /\ forall v, fp Fr Fw Br Bw Nr cok cur (k v)
  | TWhile a tst b k =>
      In (cur, a) Fr /\ fp Fr Fw Br Bw Nr cok cur b
      /\ fp Fr Fw Br Bw Nr cok cur k
  | TEmit e k => fp Fr Fw Br Bw Nr cok cur k
  | TPay d amt k =>
      In cur Br /\ In cur Bw /\ In d Bw
      /\ forall b, fp Fr Fw Br Bw Nr cok cur (k b)
  | TCall c arg amt k =>
      (match amt with
       | 0 => True
       | S _ => In cur Br /\ In cur Bw /\ In c Bw
       end)
      /\ cok c
      /\ forall r, fp Fr Fw Br Bw Nr cok cur (k r)
  end.

Definition code_certified (Fr Fw : list key) (Br Bw Nr : list addr)
           (cok : addr -> Prop) : Prop :=
  forall c arg, cok c -> fp Fr Fw Br Bw Nr cok c (CODE c arg).

Lemma fp_tseq :
  forall Fr Fw Br Bw Nr cok cur t1 t2,
    fp Fr Fw Br Bw Nr cok cur t1 ->
    fp Fr Fw Br Bw Nr cok cur t2 ->
    fp Fr Fw Br Bw Nr cok cur (tseq t1 t2).
Proof.
  intros Fr Fw Br Bw Nr cok cur t1.
  induction t1 as [| rv | | a v k IHk | a k IHk | a k IHk | a k IHk
                   | a tst tb IHb k IHk | e k IHk | d amt k IHk
                   | c arg amt k IHk];
    intros t2 H1 H2; cbn [tseq fp] in *.
  - exact H2.
  - exact I.
  - exact I.
  - destruct H1 as (Hw & Hr & Hk). auto.
  - destruct H1 as (Hr & Hk). split; [exact Hr | intros v; apply IHk; auto].
  - destruct H1 as (Hr & Hk). split; [exact Hr | intros v; apply IHk; auto].
  - destruct H1 as (Hr & Hk). split; [exact Hr | intros v; apply IHk; auto].
  - destruct H1 as (Hr & Hb & Hk). auto.
  - auto.
  - destruct H1 as (H1a & H1b & H1c & Hk).
    split; [exact H1a |]. split; [exact H1b |]. split; [exact H1c |].
    intros b. apply IHk; auto.
  - destruct H1 as (Hv & Hc & Hk).
    split; [exact Hv |]. split; [exact Hc |].
    intros r. apply IHk; auto.
Qed.

Definition disjoint (xs ys : list key) : Prop :=
  forall k, In k xs -> In k ys -> False.

Definition adisjoint (xs ys : list addr) : Prop :=
  forall a, In a xs -> In a ys -> False.

Lemma apply_tvs_untouched :
  forall l (b : bank) a,
    (forall s d amt, In (s, d, amt) l -> s <> a /\ d <> a) ->
    apply_tvs b l a = b a.
Proof.
  induction l as [| [[s d] amt] r IH]; cbn [apply_tvs]; intros b a Hp.
  - reflexivity.
  - destruct (Hp s d amt (or_introl eq_refl)) as [Hs Hd].
    rewrite IH by (intros s0 d0 a0 Hin; apply (Hp s0 d0 a0); right; exact Hin).
    rewrite (bupd_other _ d _ a) by congruence.
    rewrite (bupd_other _ s _ a) by congruence.
    reflexivity.
Qed.

Ltac fp_leaf HW :=
  refine (conj _ (conj _ (conj _ (conj _ _)))); intros; try contradiction;
  apply HW; assumption.

Lemma fp_sound :
  forall f gas cur t rd brd nrd n bn nn w cred deb acc aacc
         Fr Fw Br Bw Nr cok,
    code_certified Fr Fw Br Bw Nr cok ->
    fp Fr Fw Br Bw Nr cok cur t ->
    (forall k, In k (map fst w) -> In k Fw) ->
    (forall k v, In (k, v)
        (o_slog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> In k Fr)
    /\ (forall k, In k (map fst
        (o_buf (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc))) -> In k Fw)
    /\ (forall a v, In (a, v)
        (o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> In a Br)
    /\ (forall a v, In (a, v)
        (o_nlog (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) -> In a Nr)
    /\ (forall s d amt, In (s, d, amt)
        (o_tvs (runp f gas cur t rd brd nrd n bn nn w cred deb acc aacc)) ->
        In s Bw /\ In d Bw).
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb acc aacc
           Fr Fw Br Bw Nr cok Hcode Hfp HW;
    destruct t as [| rv | | a v k | a k | a k | a k | a tst tb k | e k
                   | d amt k | c arg amt k];
    cbn [fp] in Hfp; simpl;
    try (fp_leaf HW).
  - (* TWrite *)
    destruct Hfp as (HinW & HinR & Hfp').
    assert (HW' : forall k0, In k0 (map fst (((cur, a), v) :: w)) -> In k0 Fw).
    { intros k0 Hk0. cbn in Hk0. destruct Hk0 as [<- | Hk0].
      - exact HinW.
      - exact (HW k0 Hk0). }
    destruct (wlookup w (cur, a)) as [cv |] eqn:Hlk.
    + destruct (wcost cv v (kcold (cur, a) acc) <=? gas) eqn:Hg;
        [| fp_leaf HW].
      apply (IH (gas - wcost cv v (kcold (cur, a) acc)) cur k rd brd nrd
                n bn nn (((cur, a), v) :: w) cred deb ((cur, a) :: acc) aacc
                Fr Fw Br Bw Nr cok Hcode Hfp' HW').
    + destruct (wcost (rd n (cur, a)) v (kcold (cur, a) acc) <=? gas) eqn:Hg.
      * destruct (IH (gas - wcost (rd n (cur, a)) v (kcold (cur, a) acc)) cur
                     k rd brd nrd (S n) bn nn (((cur, a), v) :: w) cred deb
                     ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok Hcode Hfp' HW')
          as (A & B & Cc & D & E).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin;
            destruct Hin as [He | Hin];
            [injection He as <- <-; exact HinR | exact (A k0 v0 Hin)]
          | exact B | exact Cc | exact D | exact E ].
      * refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin;
            destruct Hin as [He | []];
            injection He as <- <-; exact HinR
          | exact HW
          | intros ? ? Hx; destruct Hx
          | intros ? ? Hx; destruct Hx
          | intros ? ? ? Hx; destruct Hx ].
  - (* TRead *)
    destruct Hfp as (HinR & Hfp').
    destruct (c_read C + kcold (cur, a) acc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hlk.
    + apply (IH (gas - (c_read C + kcold (cur, a) acc)) cur (k v0) rd brd nrd
                n bn nn w cred deb ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok
                Hcode (Hfp' v0) HW).
    + destruct (IH (gas - (c_read C + kcold (cur, a) acc)) cur
                   (k (rd n (cur, a))) rd brd nrd (S n) bn nn w cred deb
                   ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok Hcode
                   (Hfp' (rd n (cur, a))) HW)
        as (A & B & Cc & D & E).
      refine (conj _ (conj _ (conj _ (conj _ _))));
        [ intros k0 v0 Hin; cbn in Hin;
          destruct Hin as [He | Hin];
          [injection He as <- <-; exact HinR | exact (A k0 v0 Hin)]
        | exact B | exact Cc | exact D | exact E ].
  - (* TBal *)
    destruct Hfp as (HinB & Hfp').
    destruct (c_bal C + acold a aacc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct (IH (gas - (c_bal C + acold a aacc)) cur
                 (k (brd bn a + cred a - deb a)) rd brd nrd n (S bn) nn w
                 cred deb acc (a :: aacc) Fr Fw Br Bw Nr cok Hcode
                 (Hfp' (brd bn a + cred a - deb a)) HW)
      as (A & B & Cc & D & E).
    refine (conj _ (conj _ (conj _ (conj _ _))));
      [ exact A | exact B
      | intros a0 v0 Hin; cbn in Hin;
        destruct Hin as [He | Hin];
        [injection He as <- <-; exact HinB | exact (Cc a0 v0 Hin)]
      | exact D | exact E ].
  - (* TNonce *)
    destruct Hfp as (HinN & Hfp').
    destruct (c_nonce C + acold a aacc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct (IH (gas - (c_nonce C + acold a aacc)) cur (k (nrd nn a))
                 rd brd nrd n bn (S nn) w cred deb acc (a :: aacc)
                 Fr Fw Br Bw Nr cok Hcode (Hfp' (nrd nn a)) HW)
      as (A & B & Cc & D & E).
    refine (conj _ (conj _ (conj _ (conj _ _))));
      [ exact A | exact B | exact Cc
      | intros a0 v0 Hin; cbn in Hin;
        destruct Hin as [He | Hin];
        [injection He as <- <-; exact HinN | exact (D a0 v0 Hin)]
      | exact E ].
  - (* TWhile *)
    destruct Hfp as (HinR & Hfpb & Hfpk).
    assert (Hun : fp Fr Fw Br Bw Nr cok cur (tseq tb (TWhile a tst tb k))).
    { apply fp_tseq; [exact Hfpb |].
      cbn [fp]. exact (conj HinR (conj Hfpb Hfpk)). }
    destruct (c_while C + kcold (cur, a) acc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hlk.
    + destruct (tst v0) eqn:Hz.
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                  (tseq tb (TWhile a tst tb k)) rd brd nrd n bn nn w cred deb
                  ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok Hcode Hun HW).
      * apply (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd nrd
                  n bn nn w cred deb ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok
                  Hcode Hfpk HW).
    + destruct (tst (rd n (cur, a))) eqn:Hz.
      * destruct (IH (gas - (c_while C + kcold (cur, a) acc)) cur
                     (tseq tb (TWhile a tst tb k)) rd brd nrd (S n) bn nn w
                     cred deb ((cur, a) :: acc) aacc Fr Fw Br Bw Nr cok Hcode
                     Hun HW)
          as (A & B & Cc & D & E).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin;
            destruct Hin as [He | Hin];
            [injection He as <- <-; exact HinR | exact (A k0 v0 Hin)]
          | exact B | exact Cc | exact D | exact E ].
      * destruct (IH (gas - (c_while C + kcold (cur, a) acc)) cur k rd brd
                     nrd (S n) bn nn w cred deb ((cur, a) :: acc) aacc
                     Fr Fw Br Bw Nr cok Hcode Hfpk HW)
          as (A & B & Cc & D & E).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin;
            destruct Hin as [He | Hin];
            [injection He as <- <-; exact HinR | exact (A k0 v0 Hin)]
          | exact B | exact Cc | exact D | exact E ].
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg; [| fp_leaf HW].
    apply (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb acc aacc
              Fr Fw Br Bw Nr cok Hcode Hfp HW).
  - (* TPay *)
    destruct Hfp as (HB1 & HW1 & HW2 & Hfp').
    destruct (c_pay C + acold d aacc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp.
    + destruct (IH (gas - (c_pay C + acold d aacc)) cur (k true) rd brd nrd
                   n (S bn) nn w (bupd cred d (cred d + amt))
                   (bupd deb cur (deb cur + amt)) acc (d :: aacc)
                   Fr Fw Br Bw Nr cok Hcode (Hfp' true) HW)
        as (A & B & Cc & D & E).
      refine (conj _ (conj _ (conj _ (conj _ _))));
        [ exact A | exact B
        | intros a0 v0 Hin; cbn in Hin;
          destruct Hin as [He | Hin];
          [injection He as <- <-; exact HB1 | exact (Cc a0 v0 Hin)]
        | exact D
        | intros s0 d0 a0 Hin; cbn in Hin;
          destruct Hin as [He | Hin];
          [injection He as <- <- <-; exact (conj HW1 HW2)
          | exact (E s0 d0 a0 Hin)] ].
    + destruct (IH (gas - (c_pay C + acold d aacc)) cur (k false) rd brd nrd
                   n (S bn) nn w cred deb acc (d :: aacc)
                   Fr Fw Br Bw Nr cok Hcode (Hfp' false) HW)
        as (A & B & Cc & D & E).
      refine (conj _ (conj _ (conj _ (conj _ _))));
        [ exact A | exact B
        | intros a0 v0 Hin; cbn in Hin;
          destruct Hin as [He | Hin];
          [injection He as <- <-; exact HB1 | exact (Cc a0 v0 Hin)]
        | exact D | exact E ].
  - (* TCall *)
    destruct Hfp as (Hval & Hcok & Hfp').
    pose proof (Hcode c arg Hcok) as Hfpc.
    destruct (c_call C + acold c aacc <=? gas) eqn:Hg; [| fp_leaf HW].
    destruct amt as [| amt'].
    + set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                      rd brd nrd n bn nn w cred deb acc (c :: aacc)) in *.
      destruct (IH (gas - (c_call C + acold c aacc)) c (CODE c arg) rd brd
                   nrd n bn nn w cred deb acc (c :: aacc) Fr Fw Br Bw Nr cok
                   Hcode Hfpc HW)
        as (A1 & B1 & C1 & D1 & E1).
      fold oc in A1, B1, C1, D1, E1.
      destruct (o_ok oc) eqn:Hok.
      * destruct (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                     (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc) (o_cred oc)
                     (o_deb oc) (o_acc oc) (o_aacc oc) Fr Fw Br Bw Nr cok
                     Hcode (Hfp' (Some (o_ret oc))) B1)
          as (A2 & B2 & C2 & D2 & E2).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)]
          | exact B2
          | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (C1 a0 v0 Hin) | exact (C2 a0 v0 Hin)]
          | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (D1 a0 v0 Hin) | exact (D2 a0 v0 Hin)]
          | intros s0 d0 a0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (E1 s0 d0 a0 Hin) | exact (E2 s0 d0 a0 Hin)] ].
      * destruct (IH (o_gas oc) cur (k None) rd brd nrd
                     (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc (c :: aacc)
                     Fr Fw Br Bw Nr cok Hcode (Hfp' None) HW)
          as (A2 & B2 & C2 & D2 & E2).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ intros k0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)]
          | exact B2
          | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (C1 a0 v0 Hin) | exact (C2 a0 v0 Hin)]
          | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
            destruct Hin as [Hin | Hin];
            [exact (D1 a0 v0 Hin) | exact (D2 a0 v0 Hin)]
          | exact E2 ].
    + destruct Hval as (HB1 & HW1 & HW2).
      destruct (S amt' <=? brd bn cur + cred cur - deb cur) eqn:Hp.
      * set (oc := runp f' (gas - (c_call C + acold c aacc)) c (CODE c arg)
                        rd brd nrd n (S bn) nn w
                        (bupd cred c (cred c + S amt'))
                        (bupd deb cur (deb cur + S amt'))
                        acc (c :: aacc)) in *.
        destruct (IH (gas - (c_call C + acold c aacc)) c (CODE c arg) rd brd
                     nrd n (S bn) nn w (bupd cred c (cred c + S amt'))
                     (bupd deb cur (deb cur + S amt')) acc (c :: aacc)
                     Fr Fw Br Bw Nr cok Hcode Hfpc HW)
          as (A1 & B1 & C1 & D1 & E1).
        fold oc in A1, B1, C1, D1, E1.
        destruct (o_ok oc) eqn:Hok.
        -- destruct (IH (o_gas oc) cur (k (Some (o_ret oc))) rd brd nrd
                        (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc) (o_cred oc)
                        (o_deb oc) (o_acc oc) (o_aacc oc) Fr Fw Br Bw Nr cok
                        Hcode (Hfp' (Some (o_ret oc))) B1)
             as (A2 & B2 & C2 & D2 & E2).
           refine (conj _ (conj _ (conj _ (conj _ _))));
             [ intros k0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)]
             | exact B2
             | intros a0 v0 Hin; cbn in Hin;
               destruct Hin as [He | Hin];
               [injection He as <- <-; exact HB1 |];
               apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (C1 a0 v0 Hin) | exact (C2 a0 v0 Hin)]
             | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (D1 a0 v0 Hin) | exact (D2 a0 v0 Hin)]
             | intros s0 d0 a0 Hin; cbn in Hin;
               destruct Hin as [He | Hin];
               [injection He as <- <- <-; exact (conj HW1 HW2) |];
               apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (E1 s0 d0 a0 Hin) | exact (E2 s0 d0 a0 Hin)] ].
        -- destruct (IH (o_gas oc) cur (k None) rd brd nrd
                        (o_n oc) (o_bn oc) (o_nn oc) w cred deb acc
                        (c :: aacc) Fr Fw Br Bw Nr cok Hcode (Hfp' None) HW)
             as (A2 & B2 & C2 & D2 & E2).
           refine (conj _ (conj _ (conj _ (conj _ _))));
             [ intros k0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)]
             | exact B2
             | intros a0 v0 Hin; cbn in Hin;
               destruct Hin as [He | Hin];
               [injection He as <- <-; exact HB1 |];
               apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (C1 a0 v0 Hin) | exact (C2 a0 v0 Hin)]
             | intros a0 v0 Hin; cbn in Hin; apply in_app_or in Hin;
               destruct Hin as [Hin | Hin];
               [exact (D1 a0 v0 Hin) | exact (D2 a0 v0 Hin)]
             | exact E2 ].
      * destruct (IH (gas - (c_call C + acold c aacc)) cur (k None) rd brd
                     nrd n (S bn) nn w cred deb acc (c :: aacc)
                     Fr Fw Br Bw Nr cok Hcode (Hfp' None) HW)
          as (A2 & B2 & C2 & D2 & E2).
        refine (conj _ (conj _ (conj _ (conj _ _))));
          [ exact A2 | exact B2
          | intros a0 v0 Hin; cbn in Hin;
            destruct Hin as [He | Hin];
            [injection He as <- <-; exact HB1 | exact (C2 a0 v0 Hin)]
          | exact D2 | exact E2 ].
Qed.

(** ** Statically certified conflict freedom

    A block whose items carry certified pairwise-disjoint static footprints
    merges from base-state speculation without a single conflict: writes
    against later reads for storage, and the committed bank and nonce
    effects, the sponsor, the coinbase, and the transfer parties, against
    later balance and nonce reads. *)

Lemma static_go :
  forall ts (FRs FWs : list (list key)) (BRs BWs NRs : list (list addr))
         (cok : addr -> Prop)
         (st0 : storage) (bk0 : bank) (nm0 : nonces)
         (stp : storage) (bkp : bank) (nmp : nonces)
         (W : list key) (WB WN : list addr),
    length FRs = length ts ->
    length FWs = length ts ->
    length BRs = length ts ->
    length BWs = length ts ->
    length NRs = length ts ->
    (forall j fee non t g p FR FW BR BW NR,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        nth_error BRs j = Some BR ->
        nth_error BWs j = Some BW ->
        nth_error NRs j = Some NR ->
        fp FR FW BR BW NR cok fee t
        /\ code_certified FR FW BR BW NR cok) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    (forall j k fee non t g p BWj BRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error BWs j = Some BWj ->
        nth_error BRs k = Some BRk ->
        adisjoint (fee :: CB :: BWj) BRk) ->
    (forall j k fee non t g p NRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error NRs k = Some NRk ->
        ~ In fee NRk) ->
    (forall j FRj, nth_error FRs j = Some FRj -> disjoint W FRj) ->
    (forall j BRj, nth_error BRs j = Some BRj -> adisjoint WB BRj) ->
    (forall j NRj, nth_error NRs j = Some NRj -> adisjoint WN NRj) ->
    (forall kk, ~ In kk W -> stp kk = st0 kk) ->
    (forall a, ~ In a WB -> bkp a = bk0 a) ->
    (forall a, ~ In a WN -> nmp a = nm0 a) ->
    snd (omerge (stp, bkp, nmp) ts
          (map (fun _ => (of_state st0, of_bank bk0, of_nonces nm0)) ts))
    = 0.
Proof.
  induction ts as [| i rest IH];
    intros FRs FWs BRs BWs NRs cok st0 bk0 nm0 stp bkp nmp W WB WN
           HlF HlW HlB HlBW HlN Hcert Hdsj Hbdsj Hndsj HWd HWBd HWNd
           Hag Hbag Hnag.
  - reflexivity.
  - destruct FRs as [| FR FRs']; [cbn in HlF; discriminate |].
    destruct FWs as [| FW FWs']; [cbn in HlW; discriminate |].
    destruct BRs as [| BR BRs']; [cbn in HlB; discriminate |].
    destruct BWs as [| BW BWs']; [cbn in HlBW; discriminate |].
    destruct NRs as [| NR NRs']; [cbn in HlN; discriminate |].
    cbn [length] in HlF, HlW, HlB, HlBW, HlN.
    injection HlF as HlF. injection HlW as HlW. injection HlB as HlB.
    injection HlBW as HlBW. injection HlN as HlN.
    destruct i as [[[[fee non] t] g] p].
    destruct (Hcert 0 fee non t g p FR FW BR BW NR eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl) as [Hfp Hcode].
    unfold omerge in *.
    cbn [omergeX map hd_error tl].
    unfold mstep, cstep.
    cbn [option_map spec_out fst snd].
    destruct (gateb bkp nmp (fee, non, t, g, p)) eqn:Hgate.
    + unfold runt. cbv beta iota zeta.
      set (o := runp g (g - c_base C) fee t (of_state st0) (of_bank bk0)
                     (of_nonces nm0) 0 0 0 [] zerof (deb0 fee (g * (BF + p)))
                     [] (aacc0 fee)) in *.
      assert (Hw0 : forall kk : key, In kk (map fst ([] : buffer)) -> In kk FW)
        by (intros kk Hk; destruct Hk).
      destruct (fp_sound g (g - c_base C) fee t (of_state st0) (of_bank bk0)
                  (of_nonces nm0) 0 0 0 [] zerof (deb0 fee (g * (BF + p)))
                  [] (aacc0 fee) FR FW BR BW NR cok Hcode Hfp Hw0)
        as (HA & HB & HC & HD & HE).
      fold o in HA, HB, HC, HD, HE.
      assert (Evs : valid stp (o_slog o) = true).
      { eapply valid_stable.
        - unfold o. apply valid_self_s.
        - intros kk Hin. apply in_map_iff in Hin.
          destruct Hin as [[k1 v1] [Hf Hp1]]. cbn in Hf. subst k1.
          apply Hag. intro HkW.
          exact (HWd 0 FR eq_refl kk HkW (HA kk v1 Hp1)). }
      assert (Evb : bvalid bkp (o_blog o) = true).
      { eapply bvalid_stable.
        - unfold o. apply bvalid_self_b.
        - intros a0 Hin. apply in_map_iff in Hin.
          destruct Hin as [[a1 v1] [Hf Hp1]]. cbn in Hf. subst a1.
          apply Hbag. intro HaWB.
          exact (HWBd 0 BR eq_refl a0 HaWB (HC a0 v1 Hp1)). }
      assert (Evn : nvalid nmp (o_nlog o) = true).
      { unfold nvalid. eapply bvalid_stable.
        - unfold o.
          pose proof (nvalid_self_n g (g - c_base C) fee t (of_state st0)
                        (of_bank bk0) nm0 0 0 0 [] zerof
                        (deb0 fee (g * (BF + p))) [] (aacc0 fee)) as Hn.
          unfold nvalid in Hn. exact Hn.
        - intros a0 Hin. apply in_map_iff in Hin.
          destruct Hin as [[a1 v1] [Hf Hp1]]. cbn in Hf. subst a1.
          apply Hnag. intro HaWN.
          exact (HWNd 0 NR eq_refl a0 HaWN (HD a0 v1 Hp1)). }
      assert (Hv : vcheck stp bkp nmp o = true).
      { unfold vcheck. rewrite Evs, Evb, Evn. reflexivity. }
      rewrite Hv.
      unfold finish. cbv zeta.
      destruct (o_ok o) eqn:Hok; cbv beta iota.
      * match goal with
        | |- context [omergeX ?M rest ?SPS] =>
            assert (HI : snd (omerge M rest SPS) = 0)
        end.
        { apply (IH FRs' FWs' BRs' BWs' NRs' cok st0 bk0 nm0 _ _ _
                    (FW ++ W) (fee :: CB :: BW ++ WB) (fee :: WN));
            try assumption.
          - intros j fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0
                   E1 E2 E3 E4 E5 E6.
            exact (Hcert (S j) fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0
                     E1 E2 E3 E4 E5 E6).
          - intros j k FWj FRk Hjk E1 E2.
            exact (Hdsj (S j) (S k) FWj FRk ltac:(lia) E1 E2).
          - intros j k fee0 non0 t0 g0 p0 BWj BRk Hjk E1 E2 E3.
            exact (Hbdsj (S j) (S k) fee0 non0 t0 g0 p0 BWj BRk ltac:(lia)
                     E1 E2 E3).
          - intros j k fee0 non0 t0 g0 p0 NRk Hjk E1 E2.
            exact (Hndsj (S j) (S k) fee0 non0 t0 g0 p0 NRk ltac:(lia) E1 E2).
          - intros j FRj Ej kk HkW HkR.
            apply in_app_or in HkW. destruct HkW as [HkFW | HkW].
            + exact (Hdsj 0 (S j) FW FRj (Nat.lt_0_succ j) eq_refl Ej
                       kk HkFW HkR).
            + exact (HWd (S j) FRj Ej kk HkW HkR).
          - intros j BRj Ej a0 HaW HaR.
            cbn in HaW. destruct HaW as [<- | [<- | HaW]].
            + exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                       eq_refl eq_refl Ej fee (or_introl eq_refl) HaR).
            + exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                       eq_refl eq_refl Ej CB (or_intror (or_introl eq_refl))
                       HaR).
            + apply in_app_or in HaW. destruct HaW as [HaBW | HaWB].
              * exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                         eq_refl eq_refl Ej a0
                         (or_intror (or_intror HaBW)) HaR).
              * exact (HWBd (S j) BRj Ej a0 HaWB HaR).
          - intros j NRj Ej a0 HaW HaR.
            cbn in HaW. destruct HaW as [<- | HaW].
            + exact (Hndsj 0 (S j) fee non t g p NRj (Nat.lt_0_succ j)
                       eq_refl Ej HaR).
            + exact (HWNd (S j) NRj Ej a0 HaW HaR).
          - intros kk Hnin.
            assert (HnFW : ~ In kk (map fst (o_buf o))).
            { intro Hx. apply Hnin. apply in_or_app. left. exact (HB kk Hx). }
            rewrite (commit_untouched (o_buf o) stp kk HnFW).
            apply Hag. intro HxW. apply Hnin. apply in_or_app. right.
            exact HxW.
          - intros a0 Hnin.
            assert (Hafee : a0 <> fee)
              by (intro; subst; apply Hnin; left; reflexivity).
            assert (Hacb : a0 <> CB)
              by (intro; subst; apply Hnin; right; left; reflexivity).
            assert (HaBW : ~ In a0 BW).
            { intro Hx. apply Hnin. right. right. apply in_or_app. left.
              exact Hx. }
            assert (HaWB : ~ In a0 WB).
            { intro Hx. apply Hnin. right. right. apply in_or_app. right.
              exact Hx. }
            rewrite (bupd_other _ CB _ a0) by exact Hacb.
            rewrite (bupd_other _ fee _ a0) by exact Hafee.
            rewrite (apply_tvs_untouched (o_tvs o) _ a0)
              by (intros s0 d0 amt0 Hin;
                  destruct (HE s0 d0 amt0 Hin) as [HsB HdB];
                  split; intro; subst; [exact (HaBW HsB) | exact (HaBW HdB)]).
            rewrite (bupd_other _ fee _ a0) by exact Hafee.
            apply Hbag. exact HaWB.
          - intros a0 Hnin.
            assert (Hafee : a0 <> fee)
              by (intro; subst; apply Hnin; left; reflexivity).
            rewrite (bupd_other _ fee _ a0) by exact Hafee.
            apply Hnag. intro Hx. apply Hnin. right. exact Hx. }
        match goal with
        | |- context [omergeX ?M rest ?SPS] =>
            destruct (omergeX M rest SPS) as [[[m2 rs] fls] xs] eqn:E
        end.
        unfold omerge in HI. rewrite E in HI. cbn [snd fst] in HI.
        cbn [snd fst count_true]. lia.
      * match goal with
        | |- context [omergeX ?M rest ?SPS] =>
            assert (HI : snd (omerge M rest SPS) = 0)
        end.
        { apply (IH FRs' FWs' BRs' BWs' NRs' cok st0 bk0 nm0 _ _ _
                    (FW ++ W) (fee :: CB :: BW ++ WB) (fee :: WN));
            try assumption.
          - intros j fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0
                   E1 E2 E3 E4 E5 E6.
            exact (Hcert (S j) fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0
                     E1 E2 E3 E4 E5 E6).
          - intros j k FWj FRk Hjk E1 E2.
            exact (Hdsj (S j) (S k) FWj FRk ltac:(lia) E1 E2).
          - intros j k fee0 non0 t0 g0 p0 BWj BRk Hjk E1 E2 E3.
            exact (Hbdsj (S j) (S k) fee0 non0 t0 g0 p0 BWj BRk ltac:(lia)
                     E1 E2 E3).
          - intros j k fee0 non0 t0 g0 p0 NRk Hjk E1 E2.
            exact (Hndsj (S j) (S k) fee0 non0 t0 g0 p0 NRk ltac:(lia) E1 E2).
          - intros j FRj Ej kk HkW HkR.
            apply in_app_or in HkW. destruct HkW as [HkFW | HkW].
            + exact (Hdsj 0 (S j) FW FRj (Nat.lt_0_succ j) eq_refl Ej
                       kk HkFW HkR).
            + exact (HWd (S j) FRj Ej kk HkW HkR).
          - intros j BRj Ej a0 HaW HaR.
            cbn in HaW. destruct HaW as [<- | [<- | HaW]].
            + exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                       eq_refl eq_refl Ej fee (or_introl eq_refl) HaR).
            + exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                       eq_refl eq_refl Ej CB (or_intror (or_introl eq_refl))
                       HaR).
            + apply in_app_or in HaW. destruct HaW as [HaBW | HaWB].
              * exact (Hbdsj 0 (S j) fee non t g p BW BRj (Nat.lt_0_succ j)
                         eq_refl eq_refl Ej a0
                         (or_intror (or_intror HaBW)) HaR).
              * exact (HWBd (S j) BRj Ej a0 HaWB HaR).
          - intros j NRj Ej a0 HaW HaR.
            cbn in HaW. destruct HaW as [<- | HaW].
            + exact (Hndsj 0 (S j) fee non t g p NRj (Nat.lt_0_succ j)
                       eq_refl Ej HaR).
            + exact (HWNd (S j) NRj Ej a0 HaW HaR).
          - intros kk Hnin.
            apply Hag. intro HxW. apply Hnin. apply in_or_app. right.
            exact HxW.
          - intros a0 Hnin.
            assert (Hafee : a0 <> fee)
              by (intro; subst; apply Hnin; left; reflexivity).
            assert (Hacb : a0 <> CB)
              by (intro; subst; apply Hnin; right; left; reflexivity).
            assert (HaWB : ~ In a0 WB).
            { intro Hx. apply Hnin. right. right. apply in_or_app. right.
              exact Hx. }
            rewrite (bupd_other _ CB _ a0) by exact Hacb.
            rewrite (bupd_other _ fee _ a0) by exact Hafee.
            apply Hbag. exact HaWB.
          - intros a0 Hnin.
            assert (Hafee : a0 <> fee)
              by (intro; subst; apply Hnin; left; reflexivity).
            rewrite (bupd_other _ fee _ a0) by exact Hafee.
            apply Hnag. intro Hx. apply Hnin. right. exact Hx. }
        match goal with
        | |- context [omergeX ?M rest ?SPS] =>
            destruct (omergeX M rest SPS) as [[[m2 rs] fls] xs] eqn:E
        end.
        unfold omerge in HI. rewrite E in HI. cbn [snd fst] in HI.
        cbn [snd fst count_true]. lia.
    + match goal with
      | |- context [omergeX ?M rest ?SPS] =>
          assert (HI : snd (omerge M rest SPS) = 0)
      end.
      { apply (IH FRs' FWs' BRs' BWs' NRs' cok st0 bk0 nm0 _ _ _ W WB WN);
          try assumption.
        - intros j fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0 E1 E2 E3 E4 E5 E6.
          exact (Hcert (S j) fee0 non0 t0 g0 p0 FR0 FW0 BR0 BW0 NR0
                   E1 E2 E3 E4 E5 E6).
        - intros j k FWj FRk Hjk E1 E2.
          exact (Hdsj (S j) (S k) FWj FRk ltac:(lia) E1 E2).
        - intros j k fee0 non0 t0 g0 p0 BWj BRk Hjk E1 E2 E3.
          exact (Hbdsj (S j) (S k) fee0 non0 t0 g0 p0 BWj BRk ltac:(lia)
                   E1 E2 E3).
        - intros j k fee0 non0 t0 g0 p0 NRk Hjk E1 E2.
          exact (Hndsj (S j) (S k) fee0 non0 t0 g0 p0 NRk ltac:(lia) E1 E2).
        - intros j FRj Ej. exact (HWd (S j) FRj Ej).
        - intros j BRj Ej. exact (HWBd (S j) BRj Ej).
        - intros j NRj Ej. exact (HWNd (S j) NRj Ej). }
      match goal with
      | |- context [omergeX ?M rest ?SPS] =>
          destruct (omergeX M rest SPS) as [[[m2 rs] fls] xs] eqn:E
      end.
      unfold omerge in HI. rewrite E in HI. cbn [snd fst] in HI.
      cbn [snd fst count_true]. lia.
Qed.

Theorem static_disjoint_free :
  forall ts (FRs FWs : list (list key)) (BRs BWs NRs : list (list addr))
         (cok : addr -> Prop) (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    length BRs = length ts ->
    length BWs = length ts ->
    length NRs = length ts ->
    (forall j fee non t g p FR FW BR BW NR,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        nth_error BRs j = Some BR ->
        nth_error BWs j = Some BW ->
        nth_error NRs j = Some NR ->
        fp FR FW BR BW NR cok fee t
        /\ code_certified FR FW BR BW NR cok) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    (forall j k fee non t g p BWj BRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error BWs j = Some BWj ->
        nth_error BRs k = Some BRk ->
        adisjoint (fee :: CB :: BWj) BRk) ->
    (forall j k fee non t g p NRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error NRs k = Some NRk ->
        ~ In fee NRk) ->
    snd (omerge (st, bk, nm) ts
          (map (fun _ => (of_state st, of_bank bk, of_nonces nm)) ts)) = 0.
Proof.
  intros ts FRs FWs BRs BWs NRs cok st bk nm HlF HlW HlB HlBW HlN
         Hcert Hdsj Hbdsj Hndsj.
  apply (static_go ts FRs FWs BRs BWs NRs cok st bk nm st bk nm [] [] []);
    try assumption.
  - intros j FRj _ kk Hk. destruct Hk.
  - intros j BRj _ a0 Ha. destruct Ha.
  - intros j NRj _ a0 Ha. destruct Ha.
  - intros kk _. reflexivity.
  - intros a0 _. reflexivity.
  - intros a0 _. reflexivity.
Qed.

Theorem work_disjoint :
  forall ts (FRs FWs : list (list key)) (BRs BWs NRs : list (list addr))
         (cok : addr -> Prop) (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    length BRs = length ts ->
    length BWs = length ts ->
    length NRs = length ts ->
    (forall j fee non t g p FR FW BR BW NR,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        nth_error BRs j = Some BR ->
        nth_error BWs j = Some BW ->
        nth_error NRs j = Some NR ->
        fp FR FW BR BW NR cok fee t
        /\ code_certified FR FW BR BW NR cok) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    (forall j k fee non t g p BWj BRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error BWs j = Some BWj ->
        nth_error BRs k = Some BRk ->
        adisjoint (fee :: CB :: BWj) BRk) ->
    (forall j k fee non t g p NRk,
        j < k ->
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error NRs k = Some NRk ->
        ~ In fee NRk) ->
    executions (st, bk, nm) ts
      (map (fun _ => (of_state st, of_bank bk, of_nonces nm)) ts)
    = nonrejected (snd (seq_execr (st, bk, nm) ts)).
Proof.
  intros ts FRs FWs BRs BWs NRs cok st bk nm HlF HlW HlB HlBW HlN
         Hcert Hdsj Hbdsj Hndsj.
  rewrite executions_law.
  rewrite (static_disjoint_free ts FRs FWs BRs BWs NRs cok st bk nm
             HlF HlW HlB HlBW HlN Hcert Hdsj Hbdsj Hndsj).
  rewrite (optimistic_correct ts
             (map (fun _ => (of_state st, of_bank bk, of_nonces nm)) ts)
             (st, bk, nm)).
  lia.
Qed.

(** ** An executable footprint checker

    First-order syntax: expressions over de Bruijn variables bound by
    reads, balance and nonce queries, payment outcomes, and call results.
    [fcompile] interprets it into the transaction language; [xfoot]
    computes footprints and [xcalls] called contracts on the syntax alone,
    so certification of compiled programs is a boolean computation.  A
    call whose amount is not the literal zero is charged the value-call
    footprint conservatively. *)

Inductive fexpr : Type :=
| FVar : nat -> fexpr
| FConst : nat -> fexpr
| FAdd : fexpr -> fexpr -> fexpr
| FSub : fexpr -> fexpr -> fexpr
| FMul : fexpr -> fexpr -> fexpr.

Fixpoint feval (env : list val) (e : fexpr) : val :=
  match e with
  | FVar i => nth i env 0
  | FConst n => n
  | FAdd a b => feval env a + feval env b
  | FSub a b => feval env a - feval env b
  | FMul a b => feval env a * feval env b
  end.

Inductive ftx : Type :=
| XDone : ftx
| XRet : fexpr -> ftx
| XRevert : ftx
| XWrite : addr -> fexpr -> ftx -> ftx
| XRead : addr -> ftx -> ftx
| XBal : addr -> ftx -> ftx
| XNonce : addr -> ftx -> ftx
| XWhile : addr -> ftx -> ftx -> ftx
| XEmit : fexpr -> ftx -> ftx
| XPay : addr -> fexpr -> ftx -> ftx
| XCall : addr -> fexpr -> fexpr -> ftx -> ftx.

Fixpoint fcompile (env : list val) (x : ftx) : tx :=
  match x with
  | XDone => TDone
  | XRet e => TRet (feval env e)
  | XRevert => TRevert
  | XWrite a e k => TWrite a (feval env e) (fcompile env k)
  | XRead a k => TRead a (fun v => fcompile (v :: env) k)
  | XBal a k => TBal a (fun v => fcompile (v :: env) k)
  | XNonce a k => TNonce a (fun v => fcompile (v :: env) k)
  | XWhile a b k =>
      TWhile a (fun v => negb (v =? 0)) (fcompile env b) (fcompile env k)
  | XEmit e k => TEmit (feval env e) (fcompile env k)
  | XPay d e k =>
      TPay d (feval env e)
           (fun ok => fcompile ((if ok then 1 else 0) :: env) k)
  | XCall c earg eamt k =>
      TCall c (feval env earg) (feval env eamt)
        (fun r => match r with
                  | Some rv => fcompile (rv :: 1 :: env) k
                  | None => fcompile (0 :: 0 :: env) k
                  end)
  end.

Record foot : Type := Foot {
  f_fr : list key; f_fw : list key;
  f_br : list addr; f_bw : list addr; f_nr : list addr
}.

Definition f0 : foot := Foot [] [] [] [] [].

Definition fjoin (a b : foot) : foot :=
  Foot (f_fr a ++ f_fr b) (f_fw a ++ f_fw b) (f_br a ++ f_br b)
       (f_bw a ++ f_bw b) (f_nr a ++ f_nr b).

Definition amt_static0 (e : fexpr) : bool :=
  match e with FConst 0 => true | _ => false end.

Fixpoint xfoot (cur : addr) (x : ftx) : foot :=
  match x with
  | XDone | XRet _ | XRevert => f0
  | XWrite a _ k =>
      fjoin (Foot [(cur, a)] [(cur, a)] [] [] []) (xfoot cur k)
  | XRead a k => fjoin (Foot [(cur, a)] [] [] [] []) (xfoot cur k)
  | XBal a k => fjoin (Foot [] [] [a] [] []) (xfoot cur k)
  | XNonce a k => fjoin (Foot [] [] [] [] [a]) (xfoot cur k)
  | XWhile a b k =>
      fjoin (Foot [(cur, a)] [] [] [] [])
            (fjoin (xfoot cur b) (xfoot cur k))
  | XEmit _ k => xfoot cur k
  | XPay d _ k => fjoin (Foot [] [] [cur] [cur; d] []) (xfoot cur k)
  | XCall c _ eamt k =>
      fjoin (if amt_static0 eamt then f0 else Foot [] [] [cur] [cur; c] [])
            (xfoot cur k)
  end.

Fixpoint xcalls (x : ftx) : list addr :=
  match x with
  | XDone | XRet _ | XRevert => []
  | XWrite _ _ k => xcalls k
  | XRead _ k => xcalls k
  | XBal _ k => xcalls k
  | XNonce _ k => xcalls k
  | XWhile _ b k => xcalls b ++ xcalls k
  | XEmit _ k => xcalls k
  | XPay _ _ k => xcalls k
  | XCall c _ _ k => c :: xcalls k
  end.

Lemma inaddr_in : forall a l, inaddr a l = true <-> In a l.
Proof.
  intros a l. unfold inaddr. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply Nat.eqb_eq in He. subst. exact Hx.
  - intros Hx. exists a. split; [exact Hx | apply Nat.eqb_refl].
Qed.

Lemma inkey_in : forall k l, inkey k l = true <-> In k l.
Proof.
  intros k l. unfold inkey. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply keqb_eq in He. subst. exact Hx.
  - intros Hx. exists k. split; [exact Hx | apply keqb_refl].
Qed.

Definition subsetb (xs ys : list addr) : bool :=
  forallb (fun a => inaddr a ys) xs.

Lemma subsetb_incl : forall xs ys, subsetb xs ys = true -> incl xs ys.
Proof.
  intros xs ys Hs a Ha. unfold subsetb in Hs.
  rewrite forallb_forall in Hs.
  apply inaddr_in. exact (Hs a Ha).
Qed.

Definition ksubsetb (xs ys : list key) : bool :=
  forallb (fun k => inkey k ys) xs.

Lemma ksubsetb_incl : forall xs ys, ksubsetb xs ys = true -> incl xs ys.
Proof.
  intros xs ys Hs k Hk. unfold ksubsetb in Hs.
  rewrite forallb_forall in Hs.
  apply inkey_in. exact (Hs k Hk).
Qed.

Definition kdisjb (xs ys : list key) : bool :=
  forallb (fun k => negb (inkey k ys)) xs.

Lemma kdisjb_disjoint : forall xs ys, kdisjb xs ys = true -> disjoint xs ys.
Proof.
  intros xs ys Hd k Hx Hy. unfold kdisjb in Hd.
  rewrite forallb_forall in Hd.
  specialize (Hd k Hx). apply inkey_in in Hy.
  rewrite Hy in Hd. discriminate.
Qed.

Definition adisjb (xs ys : list addr) : bool :=
  forallb (fun a => negb (inaddr a ys)) xs.

Lemma adisjb_adisjoint : forall xs ys, adisjb xs ys = true -> adisjoint xs ys.
Proof.
  intros xs ys Hd a Hx Hy. unfold adisjb in Hd.
  rewrite forallb_forall in Hd.
  specialize (Hd a Hx). apply inaddr_in in Hy.
  rewrite Hy in Hd. discriminate.
Qed.

Lemma xfoot_fp :
  forall x cur env Fr Fw Br Bw Nr (CS : list addr),
    incl (f_fr (xfoot cur x)) Fr ->
    incl (f_fw (xfoot cur x)) Fw ->
    incl (f_br (xfoot cur x)) Br ->
    incl (f_bw (xfoot cur x)) Bw ->
    incl (f_nr (xfoot cur x)) Nr ->
    incl (xcalls x) CS ->
    fp Fr Fw Br Bw Nr (fun c => In c CS) cur (fcompile env x).
Proof.
  induction x as [| e | | a e k IHk | a k IHk | a k IHk | a k IHk
                  | a b IHb k IHk | e k IHk | d e k IHk | c earg eamt k IHk];
    intros cur env Fr Fw Br Bw Nr CS Hfr Hfw Hbr Hbw Hnr Hcs;
    cbn [fcompile xfoot fjoin f_fr f_fw f_br f_bw f_nr xcalls fp] in *.
  - exact I.
  - exact I.
  - exact I.
  - (* XWrite *)
    apply incl_cons_inv in Hfr. destruct Hfr as [Hh1 Hfr].
    apply incl_cons_inv in Hfw. destruct Hfw as [Hh2 Hfw].
    split; [exact Hh2 |]. split; [exact Hh1 |].
    apply IHk; assumption.
  - (* XRead *)
    apply incl_cons_inv in Hfr. destruct Hfr as [Hh1 Hfr].
    split; [exact Hh1 |].
    intros v. apply IHk; assumption.
  - (* XBal *)
    apply incl_cons_inv in Hbr. destruct Hbr as [Hh1 Hbr].
    split; [exact Hh1 |].
    intros v. apply IHk; assumption.
  - (* XNonce *)
    apply incl_cons_inv in Hnr. destruct Hnr as [Hh1 Hnr].
    split; [exact Hh1 |].
    intros v. apply IHk; assumption.
  - (* XWhile *)
    apply incl_cons_inv in Hfr. destruct Hfr as [Hh1 Hfr].
    apply incl_app_inv in Hfr. destruct Hfr as [Hfr1 Hfr2].
    apply incl_app_inv in Hfw. destruct Hfw as [_ Hfw].
    apply incl_app_inv in Hfw. destruct Hfw as [Hfw1 Hfw2].
    apply incl_app_inv in Hbr. destruct Hbr as [_ Hbr].
    apply incl_app_inv in Hbr. destruct Hbr as [Hbr1 Hbr2].
    apply incl_app_inv in Hbw. destruct Hbw as [_ Hbw].
    apply incl_app_inv in Hbw. destruct Hbw as [Hbw1 Hbw2].
    apply incl_app_inv in Hnr. destruct Hnr as [_ Hnr].
    apply incl_app_inv in Hnr. destruct Hnr as [Hnr1 Hnr2].
    apply incl_app_inv in Hcs. destruct Hcs as [Hcs1 Hcs2].
    split; [exact Hh1 |].
    split; [apply IHb; assumption | apply IHk; assumption].
  - (* XEmit *)
    apply IHk; assumption.
  - (* XPay *)
    apply incl_cons_inv in Hbr. destruct Hbr as [Hh1 Hbr].
    apply incl_cons_inv in Hbw. destruct Hbw as [Hh2 Hbw].
    apply incl_cons_inv in Hbw. destruct Hbw as [Hh3 Hbw].
    split; [exact Hh1 |]. split; [exact Hh2 |]. split; [exact Hh3 |].
    intros b. apply IHk; assumption.
  - (* XCall *)
    apply incl_cons_inv in Hcs. destruct Hcs as [Hc1 Hcs].
    destruct (amt_static0 eamt) eqn:Hst.
    + (* statically zero: no bank footprint needed *)
      destruct eamt as [i | nn0 | e1 e2 | e1 e2 | e1 e2]; try discriminate.
      destruct nn0 as [| nn0]; [| discriminate].
      cbn [feval].
      split; [exact I |]. split; [exact Hc1 |].
      intros r. destruct r as [rv |]; apply IHk; assumption.
    + apply incl_cons_inv in Hbr. destruct Hbr as [Hh1 Hbr].
      apply incl_cons_inv in Hbw. destruct Hbw as [Hh2 Hbw].
      apply incl_cons_inv in Hbw. destruct Hbw as [Hh3 Hbw].
      split.
      { destruct (feval env eamt); [exact I |].
        split; [exact Hh1 |]. split; [exact Hh2 |]. exact Hh3. }
      split; [exact Hc1 |].
      intros r. destruct r as [rv |]; apply IHk; assumption.
Qed.

(** ** Whole-block checking

    [static_check] certifies a first-order block by computation: the
    certified-contract set is call-closed, every item's calls fall in it,
    and the aggregated footprints, each item's own plus the whole
    certified code library's, are pairwise disjoint in the write-read,
    bank, and nonce dimensions.  A checked block merges from base-state
    speculation without a single conflict. *)

Definition closedb (CODEX : addr -> ftx) (CS : list addr) : bool :=
  forallb (fun c => subsetb (xcalls (CODEX c)) CS) CS.

Definition csfoot (CODEX : addr -> ftx) (CS : list addr) : foot :=
  fold_right (fun c acc => fjoin (xfoot c (CODEX c)) acc) f0 CS.

Lemma csfoot_incl :
  forall CODEX CS c, In c CS ->
    incl (f_fr (xfoot c (CODEX c))) (f_fr (csfoot CODEX CS))
    /\ incl (f_fw (xfoot c (CODEX c))) (f_fw (csfoot CODEX CS))
    /\ incl (f_br (xfoot c (CODEX c))) (f_br (csfoot CODEX CS))
    /\ incl (f_bw (xfoot c (CODEX c))) (f_bw (csfoot CODEX CS))
    /\ incl (f_nr (xfoot c (CODEX c))) (f_nr (csfoot CODEX CS)).
Proof.
  intros CODEX CS. induction CS as [| c0 CS' IH]; intros c Hc;
    [contradiction |].
  cbn [csfoot fold_right] in *.
  destruct Hc as [-> | Hc].
  - repeat split; apply incl_appl; apply incl_refl.
  - destruct (IH c Hc) as (H1 & H2 & H3 & H4 & H5).
    repeat split; apply incl_appr; assumption.
Qed.

Lemma cs_code_certified :
  forall (CODEX : addr -> ftx),
    (forall c arg, CODE c arg = fcompile [arg] (CODEX c)) ->
    forall CS Fr Fw Br Bw Nr,
      closedb CODEX CS = true ->
      (forall c, In c CS ->
         incl (f_fr (xfoot c (CODEX c))) Fr /\
         incl (f_fw (xfoot c (CODEX c))) Fw /\
         incl (f_br (xfoot c (CODEX c))) Br /\
         incl (f_bw (xfoot c (CODEX c))) Bw /\
         incl (f_nr (xfoot c (CODEX c))) Nr) ->
      code_certified Fr Fw Br Bw Nr (fun c => In c CS).
Proof.
  intros CODEX HC CS Fr Fw Br Bw Nr Hcl Hin c arg Hc.
  rewrite HC.
  destruct (Hin c Hc) as (H1 & H2 & H3 & H4 & H5).
  apply xfoot_fp; try assumption.
  unfold closedb in Hcl. rewrite forallb_forall in Hcl.
  apply subsetb_incl. exact (Hcl c Hc).
Qed.

Definition fitem : Type := (addr * nat * ftx * nat * nat)%type.

Definition citem (fi : fitem) : item :=
  let '(fee, non, x, g, p) := fi in (fee, non, fcompile [] x, g, p).

Definition ifoot (CODEX : addr -> ftx) (CS : list addr) (fi : fitem) : foot :=
  let '(fee, non, x, g, p) := fi in
  fjoin (xfoot fee x) (csfoot CODEX CS).

Definition itemok (CODEX : addr -> ftx) (CS : list addr) (fi : fitem) : bool :=
  let '(fee, non, x, g, p) := fi in subsetb (xcalls x) CS.

Definition pair_ok (CODEX : addr -> ftx) (CS : list addr)
           (fi fj : fitem) : bool :=
  let Fi := ifoot CODEX CS fi in
  let Fj := ifoot CODEX CS fj in
  let '(feei, _, _, _, _) := fi in
  kdisjb (f_fw Fi) (f_fr Fj)
  && adisjb (feei :: CB :: f_bw Fi) (f_br Fj)
  && negb (inaddr feei (f_nr Fj)).

Fixpoint pairb {A : Type} (P : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: r => forallb (P x) r && pairb P r
  end.

Lemma pairb_sound :
  forall (A : Type) (P : A -> A -> bool) l,
    pairb P l = true ->
    forall j k x y, j < k ->
      nth_error l j = Some x -> nth_error l k = Some y -> P x y = true.
Proof.
  intros A P l. induction l as [| h r IH]; intros Hp j k x y Hjk Hx Hy.
  - destruct j; discriminate.
  - cbn in Hp. apply andb_true_iff in Hp. destruct Hp as [Hall Hp].
    destruct j as [| j'].
    + cbn in Hx. injection Hx as <-.
      destruct k as [| k']; [lia |]. cbn in Hy.
      rewrite forallb_forall in Hall.
      apply Hall. eapply nth_error_In. exact Hy.
    + destruct k as [| k']; [lia |]. cbn in Hx, Hy.
      exact (IH Hp j' k' x y ltac:(lia) Hx Hy).
Qed.

Lemma nth_map_inv :
  forall (A B : Type) (f : A -> B) l j y,
    nth_error (map f l) j = Some y ->
    exists x, nth_error l j = Some x /\ y = f x.
Proof.
  intros A B f l. induction l as [| h r IH]; intros j y Hy;
    destruct j as [| j']; cbn in Hy; try discriminate.
  - injection Hy as <-. exists h. auto.
  - destruct (IH j' y Hy) as [x [Hx ->]]. exists x. auto.
Qed.

Lemma map_nth_some :
  forall (A B : Type) (f : A -> B) l j x,
    nth_error l j = Some x ->
    nth_error (map f l) j = Some (f x).
Proof.
  intros A B f l. induction l as [| h r IH]; intros j x Hx;
    destruct j as [| j']; cbn in *; try discriminate.
  - injection Hx as <-. reflexivity.
  - exact (IH j' x Hx).
Qed.

Definition static_check (CODEX : addr -> ftx) (CS : list addr)
           (fis : list fitem) : bool :=
  closedb CODEX CS
  && forallb (itemok CODEX CS) fis
  && pairb (pair_ok CODEX CS) fis.

Theorem checked_disjoint_free :
  forall (CODEX : addr -> ftx),
    (forall c arg, CODE c arg = fcompile [arg] (CODEX c)) ->
    forall CS fis (st : storage) (bk : bank) (nm : nonces),
      static_check CODEX CS fis = true ->
      snd (omerge (st, bk, nm) (map citem fis)
            (map (fun _ => (of_state st, of_bank bk, of_nonces nm))
                 (map citem fis))) = 0.
Proof.
  intros CODEX HC CS fis st bk nm Hchk.
  unfold static_check in Hchk.
  apply andb_true_iff in Hchk. destruct Hchk as [Hchk Hpair].
  apply andb_true_iff in Hchk. destruct Hchk as [Hcl Hitems].
  rewrite forallb_forall in Hitems.
  apply (static_disjoint_free (map citem fis)
           (map (fun fi => f_fr (ifoot CODEX CS fi)) fis)
           (map (fun fi => f_fw (ifoot CODEX CS fi)) fis)
           (map (fun fi => f_br (ifoot CODEX CS fi)) fis)
           (map (fun fi => f_bw (ifoot CODEX CS fi)) fis)
           (map (fun fi => f_nr (ifoot CODEX CS fi)) fis)
           (fun c => In c CS));
    try (rewrite !length_map; reflexivity).
  - intros j fee non t g p FR FW BR BW NR E1 E2 E3 E4 E5 E6.
    destruct (nth_map_inv _ _ citem fis j _ E1) as [fi [Hfi Hci]].
    destruct fi as [[[[fee0 non0] x0] g0] p0].
    cbn [citem] in Hci. injection Hci as -> -> -> -> ->.
    pose proof (map_nth_some _ _ (fun fi => f_fr (ifoot CODEX CS fi))
                  fis j _ Hfi) as EF. rewrite E2 in EF. injection EF as ->.
    pose proof (map_nth_some _ _ (fun fi => f_fw (ifoot CODEX CS fi))
                  fis j _ Hfi) as EF. rewrite E3 in EF. injection EF as ->.
    pose proof (map_nth_some _ _ (fun fi => f_br (ifoot CODEX CS fi))
                  fis j _ Hfi) as EF. rewrite E4 in EF. injection EF as ->.
    pose proof (map_nth_some _ _ (fun fi => f_bw (ifoot CODEX CS fi))
                  fis j _ Hfi) as EF. rewrite E5 in EF. injection EF as ->.
    pose proof (map_nth_some _ _ (fun fi => f_nr (ifoot CODEX CS fi))
                  fis j _ Hfi) as EF. rewrite E6 in EF. injection EF as ->.
    cbn [ifoot].
    split.
    + apply xfoot_fp.
      * cbn [fjoin f_fr]. apply incl_appl. apply incl_refl.
      * cbn [fjoin f_fw]. apply incl_appl. apply incl_refl.
      * cbn [fjoin f_br]. apply incl_appl. apply incl_refl.
      * cbn [fjoin f_bw]. apply incl_appl. apply incl_refl.
      * cbn [fjoin f_nr]. apply incl_appl. apply incl_refl.
      * apply subsetb_incl.
        exact (Hitems _ (nth_error_In fis j Hfi)).
    + apply (cs_code_certified CODEX HC CS); [exact Hcl |].
      intros c Hc.
      destruct (csfoot_incl CODEX CS c Hc) as (H1 & H2 & H3 & H4 & H5).
      repeat split; cbn [fjoin f_fr f_fw f_br f_bw f_nr];
        apply incl_appr; assumption.
  - intros j k FWj FRk Hjk E1 E2.
    destruct (nth_map_inv _ _ _ fis j _ E1) as [fi [Hfi ->]].
    destruct (nth_map_inv _ _ _ fis k _ E2) as [fj [Hfj ->]].
    pose proof (pairb_sound _ _ fis Hpair j k fi fj Hjk Hfi Hfj) as Hpo.
    unfold pair_ok in Hpo.
    destruct fi as [[[[feei noni] xi] gi] pi].
    apply andb_true_iff in Hpo. destruct Hpo as [Hpo _].
    apply andb_true_iff in Hpo. destruct Hpo as [Hpo _].
    apply kdisjb_disjoint. exact Hpo.
  - intros j k fee non t g p BWj BRk Hjk E1 E2 E3.
    destruct (nth_map_inv _ _ citem fis j _ E1) as [fi [Hfi Hci]].
    destruct (nth_map_inv _ _ _ fis j _ E2) as [fi2 [Hfi2 ->]].
    assert (fi2 = fi) by congruence. subst fi2.
    destruct (nth_map_inv _ _ _ fis k _ E3) as [fj [Hfj ->]].
    pose proof (pairb_sound _ _ fis Hpair j k fi fj Hjk Hfi Hfj) as Hpo.
    unfold pair_ok in Hpo.
    destruct fi as [[[[feei noni] xi] gi] pi].
    cbn [citem] in Hci. injection Hci as -> -> -> -> ->.
    apply andb_true_iff in Hpo. destruct Hpo as [Hpo _].
    apply andb_true_iff in Hpo. destruct Hpo as [_ Hpo].
    apply adisjb_adisjoint. exact Hpo.
  - intros j k fee non t g p NRk Hjk E1 E2.
    destruct (nth_map_inv _ _ citem fis j _ E1) as [fi [Hfi Hci]].
    destruct (nth_map_inv _ _ _ fis k _ E2) as [fj [Hfj ->]].
    pose proof (pairb_sound _ _ fis Hpair j k fi fj Hjk Hfi Hfj) as Hpo.
    unfold pair_ok in Hpo.
    destruct fi as [[[[feei noni] xi] gi] pi].
    cbn [citem] in Hci. injection Hci as -> -> -> -> ->.
    apply andb_true_iff in Hpo. destruct Hpo as [_ Hpo].
    intro Hx. apply inaddr_in in Hx. rewrite Hx in Hpo. discriminate.
Qed.

(** ** The multi-version store

    [cbuf m ts j] is the write buffer position [j] commits under true
    sequential execution: its receipt buffer for a completing transaction,
    empty for a reverted or rejected one.  [mvstor m ts keep j] is the
    storage a versioned store presents to position [j]: the base storage
    overlaid, in index order, with the committed buffers of exactly the
    positions below [j] that [keep] selects.  Keeping every position
    reconstructs the true prefix storage; the agreement lemma says dropped
    positions are harmless on any key they do not write. *)

Definition cbuf (m : mach) (ts : list item) (j : nat) : buffer :=
  snd (fst (fst (snd (step (mach_at m ts j) (nth j ts ditem))))).

Fixpoint mvstor (m : mach) (ts : list item) (keep : nat -> bool) (j : nat)
  : storage :=
  match j with
  | 0 => fst (fst m)
  | S j' => if keep j'
            then commit (mvstor m ts keep j') (cbuf m ts j')
            else mvstor m ts keep j'
  end.

Lemma commit_pointwise :
  forall w (s s' : storage) k,
    s k = s' k -> commit s w k = commit s' w k.
Proof.
  induction w as [| [k0 v0] w' IH]; simpl; intros s s' k Hk.
  - exact Hk.
  - unfold kupd. destruct (keqb k k0); [reflexivity | apply IH; exact Hk].
Qed.

Lemma stor_mach_at_S :
  forall ts m j,
    j < length ts ->
    fst (fst (mach_at m ts (S j)))
    = commit (fst (fst (mach_at m ts j))) (cbuf m ts j).
Proof.
  intros ts m j Hj.
  rewrite (mach_at_S ts m j Hj).
  unfold cbuf.
  destruct (mach_at m ts j) as [[stq bkq] nmq].
  destruct (nth j ts ditem) as [[[[fee non] t] g] p].
  unfold step.
  destruct (gateb bkq nmq (fee, non, t, g, p)) eqn:Hgate.
  - unfold finish. cbv zeta.
    destruct (o_ok (runt (fee, non, t, g, p) (of_state stq) (of_bank bkq)
                         (of_nonces nmq))) eqn:Hok; cbv beta iota;
      cbn [fst snd]; reflexivity.
  - cbn [fst snd]. reflexivity.
Qed.

Lemma mvstor_agree :
  forall m ts keep (K : list key) j,
    j <= length ts ->
    (forall i, i < j -> keep i = false ->
        forall kk, In kk (map fst (cbuf m ts i)) -> ~ In kk K) ->
    forall kk, In kk K ->
      mvstor m ts keep j kk = fst (fst (mach_at m ts j)) kk.
Proof.
  intros m ts keep K.
  induction j as [| j' IH]; intros Hj Hsafe kk HinK.
  - reflexivity.
  - cbn [mvstor].
    rewrite (stor_mach_at_S ts m j') by lia.
    destruct (keep j') eqn:Hk.
    + apply commit_pointwise. apply IH; [lia | | exact HinK].
      intros i Hi Hki. apply Hsafe; [lia | exact Hki].
    + rewrite commit_untouched.
      * apply IH; [lia | | exact HinK].
        intros i Hi Hki. apply Hsafe; [lia | exact Hki].
      * intro Hx. exact (Hsafe j' (Nat.lt_succ_diag_r j') Hk kk Hx HinK).
Qed.

Lemma no_pairs_nil :
  forall (A B : Type) (l : list (A * B)),
    (forall a b, In (a, b) l -> False) -> l = [].
Proof.
  intros A B [| [a b] r] H; [reflexivity |].
  exfalso. exact (H a b (or_introl eq_refl)).
Qed.

Lemma cbuf_keys :
  forall m ts (cok : addr -> Prop) j fee non t g p FR FW,
    nth_error ts j = Some (fee, non, t, g, p) ->
    fp FR FW [] [] [] cok fee t ->
    code_certified FR FW [] [] [] cok ->
    forall kk, In kk (map fst (cbuf m ts j)) -> In kk FW.
Proof.
  intros m ts cok j fee non t g p FR FW Hi Hfp Hcode kk Hin.
  unfold cbuf in Hin.
  assert (En : @nth item j ts ditem = (fee, non, t, g, p))
    by (apply nth_error_nth; exact Hi).
  rewrite En in Hin.
  destruct (mach_at m ts j) as [[stq bkq] nmq].
  unfold step in Hin.
  destruct (gateb bkq nmq (fee, non, t, g, p)) eqn:Hgate.
  - unfold finish in Hin. cbv zeta in Hin.
    unfold runt in Hin. cbv beta iota zeta in Hin.
    assert (Hw0 : forall k0 : key, In k0 (map fst ([] : buffer)) -> In k0 FW)
      by (intros k0 Hk0; destruct Hk0).
    destruct (fp_sound g (g - c_base C) fee t (of_state stq) (of_bank bkq)
                (of_nonces nmq) 0 0 0 [] zerof (deb0 fee (g * (BF + p)))
                [] (aacc0 fee) FR FW [] [] [] cok Hcode Hfp Hw0)
      as (_ & HB & _).
    destruct (o_ok (runp g (g - c_base C) fee t (of_state stq) (of_bank bkq)
                         (of_nonces nmq) 0 0 0 [] zerof
                         (deb0 fee (g * (BF + p))) [] (aacc0 fee)))
      eqn:Hok; cbv beta iota in Hin; cbn [fst snd] in Hin.
    + exact (HB kk Hin).
    + destruct Hin.
  - cbn [fst snd] in Hin. destruct Hin.
Qed.

(** ** Estimated dependencies and versioned speculation

    [mv_go] is the engine: block positions speculate against versioned
    storages selected by an arbitrary inclusion policy [keepf], and every
    position whose policy provably covers its write-read dependencies
    validates, so conflicts are bounded by the positions [P] does not
    certify.  Certificates here are storage-pure: no balance, pay, nonce,
    or value-call footprints, so the logs a certified position must
    validate against the evolving bank and nonces are empty.  Dependency
    estimation and the parallel-depth bound are both instances. *)

Lemma mv_go :
  forall ts (ts0 : list item) (FRs FWs : list (list key)) (cok : addr -> Prop)
         (m : mach) (brd0 : breader) (nrd0 : nreader)
         (keepf : nat -> nat -> bool) (P : nat -> bool) (d : nat),
    (forall j, nth_error ts0 (d + j) = nth_error ts j) ->
    d + length ts = length ts0 ->
    length FRs = length ts0 ->
    length FWs = length ts0 ->
    (forall j fee non t g p FR FW,
        nth_error ts0 j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        fp FR FW [] [] [] cok fee t /\ code_certified FR FW [] [] [] cok) ->
    (forall j i FRj FWi,
        i < j -> j < length ts0 -> P j = true ->
        nth_error FRs j = Some FRj ->
        nth_error FWs i = Some FWi ->
        keepf j i = false -> disjoint FWi FRj) ->
    snd (omerge (mach_at m ts0 d) ts
          (map (fun j => (of_state (mvstor m ts0 (keepf j) j), brd0, nrd0))
               (seq d (length ts))))
    <= length (filter (fun j => negb (P j)) (seq d (length ts))).
Proof.
  induction ts as [| i0 rest IH];
    intros ts0 FRs FWs cok m brd0 nrd0 keepf P d Hsuf Hd HlenR HlenW
           Hcert Hsafe.
  - cbn. lia.
  - assert (Hi0 : nth_error ts0 d = Some i0).
    { specialize (Hsuf 0). rewrite Nat.add_0_r in Hsuf. exact Hsuf. }
    assert (Hdlen : d < length ts0) by (cbn [length] in Hd; lia).
    assert (HFRe : exists FR, nth_error FRs d = Some FR).
    { destruct (nth_error FRs d) eqn:E; [eauto |].
      apply nth_error_None in E. lia. }
    destruct HFRe as [FR HFR].
    assert (HFWe : exists FW, nth_error FWs d = Some FW).
    { destruct (nth_error FWs d) eqn:E; [eauto |].
      apply nth_error_None in E. lia. }
    destruct HFWe as [FW HFW].
    assert (Hsuf' : forall j, nth_error ts0 (S d + j) = nth_error rest j).
    { intros j. specialize (Hsuf (S j)).
      rewrite Nat.add_succ_r in Hsuf. exact Hsuf. }
    assert (Hd' : S d + length rest = length ts0)
      by (cbn [length] in Hd; lia).
    destruct i0 as [[[[fee non] t] g] p].
    destruct (Hcert d fee non t g p FR FW Hi0 HFR HFW) as [Hfp Hcode].
    destruct (mach_at m ts0 d) as [[stq bkq] nmq] eqn:EM.
    unfold omerge in *.
    cbn [length seq map omergeX hd_error tl].
    unfold mstep, cstep.
    cbn [option_map spec_out fst snd].
    assert (HSd : fst (step (stq, bkq, nmq) (fee, non, t, g, p))
                  = mach_at m ts0 (S d)).
    { rewrite (mach_at_S ts0 m d Hdlen).
      assert (En : @nth item d ts0 ditem = (fee, non, t, g, p))
        by (apply nth_error_nth; exact Hi0).
      rewrite En, EM. reflexivity. }
    assert (Hcnt : length (filter (fun j => negb (P j))
                            (d :: seq (S d) (length rest)))
                   = (if negb (P d) then 1 else 0)
                     + length (filter (fun j => negb (P j))
                                (seq (S d) (length rest)))).
    { cbn [filter]. destruct (negb (P d)); cbn [length]; lia. }
    rewrite Hcnt.
    destruct (gateb bkq nmq (fee, non, t, g, p)) eqn:Hgate.
    + set (s' := mvstor m ts0 (keepf d) d) in *.
      unfold runt. cbv beta iota zeta.
      set (o := runp g (g - c_base C) fee t (of_state s') brd0 nrd0 0 0 0 []
                     zerof (deb0 fee (g * (BF + p))) [] (aacc0 fee)) in *.
      assert (Hw0 : forall kk : key, In kk (map fst ([] : buffer)) -> In kk FW)
        by (intros kk Hk0; destruct Hk0).
      destruct (fp_sound g (g - c_base C) fee t (of_state s') brd0 nrd0
                  0 0 0 [] zerof (deb0 fee (g * (BF + p))) [] (aacc0 fee)
                  FR FW [] [] [] cok Hcode Hfp Hw0)
        as (HA & HB & HC & HD & HE).
      fold o in HA, HB, HC, HD, HE.
      assert (HCe : o_blog o = []).
      { apply no_pairs_nil. intros a v Hin. exact (HC a v Hin). }
      assert (HDe : o_nlog o = []).
      { apply no_pairs_nil. intros a v Hin. exact (HD a v Hin). }
      assert (Evb : bvalid bkq (o_blog o) = true) by (rewrite HCe; reflexivity).
      assert (Evn : nvalid nmq (o_nlog o) = true) by (rewrite HDe; reflexivity).
      destruct (P d) eqn:HP.
      * (* certified position: agreement, hence validation *)
        assert (Hagree : forall kk, In kk (map fst (o_slog o)) ->
                    s' kk = stq kk).
        { intros kk Hin. apply in_map_iff in Hin.
          destruct Hin as [[k1 v1] [Hf Hp1]]. cbn in Hf. subst k1.
          assert (HinFR : In kk FR) by (exact (HA kk v1 Hp1)).
          unfold s'.
          assert (Hstq : fst (fst (mach_at m ts0 d)) kk = stq kk)
            by (rewrite EM; reflexivity).
          rewrite <- Hstq.
          apply (mvstor_agree m ts0 (keepf d) FR d); [lia | | exact HinFR].
          intros i1 Hi1 Hki1 kk2 Hkk2 HinK.
          assert (Hi1len : i1 < length ts0) by lia.
          assert (HFWe1 : exists FWi, nth_error FWs i1 = Some FWi).
          { destruct (nth_error FWs i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HFWe1 as [FWi HFWi].
          assert (HIe1 : exists ii, nth_error ts0 i1 = Some ii).
          { destruct (nth_error ts0 i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HIe1 as [ii Hii].
          assert (HFRe2 : exists FRi, nth_error FRs i1 = Some FRi).
          { destruct (nth_error FRs i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HFRe2 as [FRi HFRi].
          destruct ii as [[[[fee1 non1] t1] g1] p1].
          destruct (Hcert i1 fee1 non1 t1 g1 p1 FRi FWi Hii HFRi HFWi)
            as [Hfp1 Hcode1].
          assert (HinFWi : In kk2 FWi).
          { exact (cbuf_keys m ts0 cok i1 fee1 non1 t1 g1 p1 FRi FWi Hii
                     Hfp1 Hcode1 kk2 Hkk2). }
          exact (Hsafe d i1 FR FWi Hi1 Hdlen HP HFR HFWi Hki1 kk2
                   HinFWi HinK). }
        assert (Evs : valid stq (o_slog o) = true).
        { eapply valid_stable.
          - unfold o. apply valid_self_s.
          - intros kk Hin. symmetry. apply Hagree. exact Hin. }
        assert (Hv : vcheck stq bkq nmq o = true).
        { unfold vcheck. rewrite Evs, Evb, Evn. reflexivity. }
        rewrite Hv.
        assert (Ho : runp g (g - c_base C) fee t (of_state stq) (of_bank bkq)
                          (of_nonces nmq) 0 0 0 [] zerof
                          (deb0 fee (g * (BF + p))) [] (aacc0 fee)
                     = o).
        { unfold o. apply replay.
          - intros kk vv Hin.
            exact (valid_true_In (o_slog o) stq Evs kk vv Hin).
          - intros aa vv Hin. fold o in Hin. rewrite HCe in Hin.
            destruct Hin.
          - intros aa vv Hin. fold o in Hin. rewrite HDe in Hin.
            destruct Hin. }
        assert (Hstep : step (stq, bkq, nmq) (fee, non, t, g, p)
                        = finish stq bkq nmq fee g p o).
        { unfold step. rewrite Hgate. unfold runt. cbv beta iota zeta.
          rewrite Ho. reflexivity. }
        rewrite <- Hstep.
        destruct (step (stq, bkq, nmq) (fee, non, t, g, p)) as [m1 r] eqn:ES.
        assert (Hm1 : m1 = mach_at m ts0 (S d))
          by (rewrite <- HSd; reflexivity).
        rewrite Hm1.
        specialize (IH ts0 FRs FWs cok m brd0 nrd0 keepf P (S d)
                      Hsuf' Hd' HlenR HlenW Hcert Hsafe).
        destruct (omergeX (mach_at m ts0 (S d)) rest
                    (map (fun j => (of_state (mvstor m ts0 (keepf j) j),
                                    brd0, nrd0))
                         (seq (S d) (length rest))))
          as [[[m2 rs] fls] xs].
        cbn [snd fst] in IH.
        cbn [snd fst count_true]. lia.
      * (* uncertified position: validated or conflicted, both bounded *)
        destruct (vcheck stq bkq nmq o) eqn:Ev.
        -- unfold vcheck in Ev.
           apply andb_true_iff in Ev. destruct Ev as [Ev1 Evn'].
           apply andb_true_iff in Ev1. destruct Ev1 as [Evs' Evb'].
           assert (Ho : runp g (g - c_base C) fee t (of_state stq)
                             (of_bank bkq) (of_nonces nmq) 0 0 0 [] zerof
                             (deb0 fee (g * (BF + p))) [] (aacc0 fee) = o).
           { unfold o. apply replay.
             - intros kk vv Hin.
               exact (valid_true_In (o_slog o) stq Evs' kk vv Hin).
             - intros aa vv Hin. fold o in Hin. rewrite HCe in Hin.
               destruct Hin.
             - intros aa vv Hin. fold o in Hin. rewrite HDe in Hin.
               destruct Hin. }
           assert (Hstep : step (stq, bkq, nmq) (fee, non, t, g, p)
                           = finish stq bkq nmq fee g p o).
           { unfold step. rewrite Hgate. unfold runt. cbv beta iota zeta.
             rewrite Ho. reflexivity. }
           rewrite <- Hstep.
           destruct (step (stq, bkq, nmq) (fee, non, t, g, p)) as [m1 r]
             eqn:ES.
           assert (Hm1 : m1 = mach_at m ts0 (S d))
             by (rewrite <- HSd; reflexivity).
           rewrite Hm1.
           specialize (IH ts0 FRs FWs cok m brd0 nrd0 keepf P (S d)
                         Hsuf' Hd' HlenR HlenW Hcert Hsafe).
           destruct (omergeX (mach_at m ts0 (S d)) rest
                       (map (fun j => (of_state (mvstor m ts0 (keepf j) j),
                                       brd0, nrd0))
                            (seq (S d) (length rest))))
             as [[[m2 rs] fls] xs].
           cbn [snd fst] in IH.
           cbn [snd fst count_true]. lia.
        -- destruct (step (stq, bkq, nmq) (fee, non, t, g, p)) as [m1 r]
             eqn:ES.
           assert (Hm1 : m1 = mach_at m ts0 (S d))
             by (rewrite <- HSd; reflexivity).
           rewrite Hm1.
           specialize (IH ts0 FRs FWs cok m brd0 nrd0 keepf P (S d)
                         Hsuf' Hd' HlenR HlenW Hcert Hsafe).
           destruct (omergeX (mach_at m ts0 (S d)) rest
                       (map (fun j => (of_state (mvstor m ts0 (keepf j) j),
                                       brd0, nrd0))
                            (seq (S d) (length rest))))
             as [[[m2 rs] fls] xs].
           cbn [snd fst] in IH.
           cbn [snd fst count_true negb]. lia.
    + (* rejected: the machine does not move *)
      assert (Hm1 : (stq, bkq, nmq) = mach_at m ts0 (S d)).
      { rewrite <- HSd. unfold step. rewrite Hgate. reflexivity. }
      rewrite Hm1.
      specialize (IH ts0 FRs FWs cok m brd0 nrd0 keepf P (S d)
                    Hsuf' Hd' HlenR HlenW Hcert Hsafe).
      destruct (omergeX (mach_at m ts0 (S d)) rest
                  (map (fun j => (of_state (mvstor m ts0 (keepf j) j),
                                  brd0, nrd0))
                       (seq (S d) (length rest))))
        as [[[m2 rs] fls] xs].
      cbn [snd fst] in IH.
      cbn [snd fst count_true].
      destruct (negb (P d)); lia.
Qed.

Definition inter (xs ys : list key) : bool :=
  existsb (fun k => existsb (keqb k) ys) xs.

Lemma inter_false_disjoint :
  forall xs ys, inter xs ys = false -> disjoint xs ys.
Proof.
  intros xs ys Hf k Hx Hy.
  assert (Ht : inter xs ys = true).
  { apply existsb_exists. exists k. split; [exact Hx |].
    apply existsb_exists. exists k. split; [exact Hy | apply keqb_refl]. }
  congruence.
Qed.

Lemma filter_false_in :
  forall (A : Type) (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros A f l. induction l as [| x l' IH]; intros Hf; cbn.
  - reflexivity.
  - rewrite (Hf x (or_introl eq_refl)). apply IH.
    intros y Hy. apply Hf. right. exact Hy.
Qed.

(** Position of the first occurrence in a dispatch order. *)

Fixpoint posin (ord : list nat) (x : nat) : nat :=
  match ord with
  | [] => 0
  | y :: r => if y =? x then 0 else S (posin r x)
  end.

(** Dependency estimation: an estimate [E] covering every forward
    write-read intersection, and a dispatch order placing estimated
    dependencies before their dependents, give a versioned store under
    which no position conflicts at all, against the general bound of one
    re-execution per position. *)

Theorem estimated_order_free :
  forall (ts : list item) (FRs FWs : list (list key)) (cok : addr -> Prop)
         (E : nat -> nat -> bool) (ord : list nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j fee non t g p FR FW,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        fp FR FW [] [] [] cok fee t /\ code_certified FR FW [] [] [] cok) ->
    (forall i j FWi FRj,
        i < j -> j < length ts ->
        nth_error FWs i = Some FWi ->
        nth_error FRs j = Some FRj ->
        inter FWi FRj = true -> E i j = true) ->
    (forall i j, i < j -> j < length ts -> E i j = true ->
        posin ord i < posin ord j) ->
    snd (omerge (st, bk, nm) ts
          (map (fun j => (of_state (mvstor (st, bk, nm) ts
                            (fun i => posin ord i <? posin ord j) j),
                          of_bank bk, of_nonces nm))
               (seq 0 (length ts)))) = 0.
Proof.
  intros ts FRs FWs cok E ord st bk nm HlenR HlenW Hcert HE Hresp.
  assert (Hle := mv_go ts ts FRs FWs cok (st, bk, nm) (of_bank bk)
                   (of_nonces nm)
                   (fun j i => posin ord i <? posin ord j) (fun _ => true) 0
                   (fun j => eq_refl) eq_refl HlenR HlenW Hcert).
  rewrite (filter_false_in nat (fun j => negb ((fun _ : nat => true) j)))
    in Hle.
  2:{ intros x _. reflexivity. }
  cbn [length] in Hle.
  assert (Hsafe : forall j i FRj FWi,
             i < j -> j < length ts -> (fun _ : nat => true) j = true ->
             nth_error FRs j = Some FRj ->
             nth_error FWs i = Some FWi ->
             (fun j0 i0 => posin ord i0 <? posin ord j0) j i = false ->
             disjoint FWi FRj).
  { intros j i FRj FWi Hij Hj _ HFRj HFWi Hkf.
    cbn in Hkf. apply Nat.ltb_ge in Hkf.
    destruct (inter FWi FRj) eqn:Hint.
    - exfalso.
      assert (HEt := HE i j FWi FRj Hij Hj HFWi HFRj Hint).
      assert (Hlt := Hresp i j Hij Hj HEt). lia.
    - exact (inter_false_disjoint FWi FRj Hint). }
  specialize (Hle Hsafe).
  cbn [mach_at] in Hle. cbv beta in Hle.
  lia.
Qed.

(** Parallel depth: any height function [L] that strictly increases along
    forward write-read dependencies bounds the rounds of versioned
    speculation.  Round [r] keeps every position of height at most [r];
    every position of height at most [S r] then validates, so conflicts
    are bounded by the positions above [S r], and rounds up to the
    critical path converge to none. *)

Theorem level_rounds_bound :
  forall (ts : list item) (FRs FWs : list (list key)) (cok : addr -> Prop)
         (L : nat -> nat) (r : nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j fee non t g p FR FW,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        fp FR FW [] [] [] cok fee t /\ code_certified FR FW [] [] [] cok) ->
    (forall i j FWi FRj,
        i < j -> j < length ts ->
        nth_error FWs i = Some FWi ->
        nth_error FRs j = Some FRj ->
        inter FWi FRj = true -> L i < L j) ->
    snd (omerge (st, bk, nm) ts
          (map (fun j => (of_state (mvstor (st, bk, nm) ts
                            (fun i => L i <=? r) j),
                          of_bank bk, of_nonces nm))
               (seq 0 (length ts))))
    <= length (filter (fun j => negb (L j <=? S r)) (seq 0 (length ts))).
Proof.
  intros ts FRs FWs cok L r st bk nm HlenR HlenW Hcert HL.
  assert (Hle := mv_go ts ts FRs FWs cok (st, bk, nm) (of_bank bk)
                   (of_nonces nm)
                   (fun _ i => L i <=? r) (fun j => L j <=? S r) 0
                   (fun j => eq_refl) eq_refl HlenR HlenW Hcert).
  assert (Hsafe : forall j i FRj FWi,
             i < j -> j < length ts -> (fun j0 => L j0 <=? S r) j = true ->
             nth_error FRs j = Some FRj ->
             nth_error FWs i = Some FWi ->
             (fun _ i0 : nat => L i0 <=? r) j i = false ->
             disjoint FWi FRj).
  { intros j i FRj FWi Hij Hj HPj HFRj HFWi Hkf.
    cbn in HPj, Hkf.
    apply Nat.leb_le in HPj. apply Nat.leb_gt in Hkf.
    destruct (inter FWi FRj) eqn:Hint.
    - exfalso.
      assert (Hlt := HL i j FWi FRj Hij Hj HFWi HFRj Hint). lia.
    - exact (inter_false_disjoint FWi FRj Hint). }
  specialize (Hle Hsafe).
  cbn [mach_at] in Hle.
  exact Hle.
Qed.

Theorem level_rounds_converge :
  forall (ts : list item) (FRs FWs : list (list key)) (cok : addr -> Prop)
         (L : nat -> nat) (r : nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j fee non t g p FR FW,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        fp FR FW [] [] [] cok fee t /\ code_certified FR FW [] [] [] cok) ->
    (forall i j FWi FRj,
        i < j -> j < length ts ->
        nth_error FWs i = Some FWi ->
        nth_error FRs j = Some FRj ->
        inter FWi FRj = true -> L i < L j) ->
    (forall j, j < length ts -> L j <= S r) ->
    snd (omerge (st, bk, nm) ts
          (map (fun j => (of_state (mvstor (st, bk, nm) ts
                            (fun i => L i <=? r) j),
                          of_bank bk, of_nonces nm))
               (seq 0 (length ts)))) = 0.
Proof.
  intros ts FRs FWs cok L r st bk nm HlenR HlenW Hcert HL Hmax.
  assert (Hle := level_rounds_bound ts FRs FWs cok L r st bk nm
                   HlenR HlenW Hcert HL).
  rewrite (filter_false_in nat (fun j => negb (L j <=? S r))) in Hle.
  2:{ intros x Hx. apply in_seq in Hx.
      assert (Hlx : L x <= S r) by (apply Hmax; lia).
      apply Nat.leb_le in Hlx. rewrite Hlx. reflexivity. }
  cbn [length] in Hle.
  lia.
Qed.

(** ** The critical path, constructed

    [levels] computes a height function from the footprints themselves:
    each position's level is one more than the maximum level among earlier
    positions whose write set intersects its read set.  It strictly
    increases along forward write-read dependencies, so it instantiates
    the parallel-depth bounds with no user-supplied height function. *)

Fixpoint lvl (prev : list (list key * nat)) (FRj : list key) : nat :=
  match prev with
  | [] => 0
  | (FWi, Li) :: r =>
      Nat.max (if inter FWi FRj then S Li else 0) (lvl r FRj)
  end.

Fixpoint levels_go (fps : list (list key * list key))
         (prev : list (list key * nat)) : list nat :=
  match fps with
  | [] => []
  | (FRj, FWj) :: r =>
      lvl prev FRj :: levels_go r (prev ++ [(FWj, lvl prev FRj)])
  end.

Definition levels (FRs FWs : list (list key)) : list nat :=
  levels_go (combine FRs FWs) [].

Definition Lcan (FRs FWs : list (list key)) (j : nat) : nat :=
  nth j (levels FRs FWs) 0.

Lemma lvl_ge :
  forall prev FR q FWq Lq,
    nth_error prev q = Some (FWq, Lq) ->
    inter FWq FR = true ->
    Lq < lvl prev FR.
Proof.
  induction prev as [| [FW0 L0] r IH]; intros FR q FWq Lq Hq Hint;
    [destruct q; discriminate |].
  destruct q as [| q']; cbn in Hq.
  - injection Hq as <- <-. cbn [lvl]. rewrite Hint. lia.
  - cbn [lvl]. pose proof (IH FR q' FWq Lq Hq Hint). lia.
Qed.

Lemma nth_error_snoc :
  forall (A : Type) (l : list A) (x : A),
    nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros A l x. induction l as [| h r IH]; cbn; [reflexivity | exact IH].
Qed.

Lemma levels_go_len :
  forall fps prev, length (levels_go fps prev) = length fps.
Proof.
  induction fps as [| [a b] r IH]; intros prev; cbn;
    [reflexivity | f_equal; apply IH].
Qed.

Lemma levels_go_lvl :
  forall fps prev j FRj FWj Lj,
    nth_error fps j = Some (FRj, FWj) ->
    nth_error (levels_go fps prev) j = Some Lj ->
    forall q FWq Lq,
      nth_error prev q = Some (FWq, Lq) ->
      inter FWq FRj = true -> Lq < Lj.
Proof.
  induction fps as [| [FR0 FW0] r IH];
    intros prev j FRj FWj Lj Hj HLj q FWq Lq Hq Hint;
    [destruct j; discriminate |].
  destruct j as [| j'].
  - cbn in Hj, HLj. injection Hj as -> ->. injection HLj as <-.
    exact (lvl_ge prev FRj q FWq Lq Hq Hint).
  - cbn in Hj, HLj.
    apply (IH (prev ++ [(FW0, lvl prev FR0)]) j' FRj FWj Lj Hj HLj q FWq Lq);
      [| exact Hint].
    rewrite nth_error_app1; [exact Hq |].
    apply nth_error_Some. rewrite Hq. discriminate.
Qed.

Lemma levels_go_spec :
  forall fps prev i j FRi FWi FRj FWj Li Lj,
    i < j ->
    nth_error fps i = Some (FRi, FWi) ->
    nth_error fps j = Some (FRj, FWj) ->
    nth_error (levels_go fps prev) i = Some Li ->
    nth_error (levels_go fps prev) j = Some Lj ->
    inter FWi FRj = true ->
    Li < Lj.
Proof.
  induction fps as [| [FR0 FW0] r IH];
    intros prev i j FRi FWi FRj FWj Li Lj Hij Hi Hj HLi HLj Hint;
    [destruct i; discriminate |].
  destruct i as [| i'].
  - cbn in Hi, HLi. injection Hi as -> ->. injection HLi as <-.
    destruct j as [| j']; [lia |]. cbn in Hj, HLj.
    apply (levels_go_lvl r (prev ++ [(FWi, lvl prev FRi)]) j' FRj FWj Lj
             Hj HLj (length prev) FWi (lvl prev FRi));
      [| exact Hint].
    apply nth_error_snoc.
  - destruct j as [| j']; [lia |]. cbn in Hi, Hj, HLi, HLj.
    exact (IH (prev ++ [(FW0, lvl prev FR0)]) i' j' FRi FWi FRj FWj Li Lj
             ltac:(lia) Hi Hj HLi HLj Hint).
Qed.

Lemma nth_error_combine :
  forall (A B : Type) (l1 : list A) (l2 : list B) n x y,
    nth_error l1 n = Some x -> nth_error l2 n = Some y ->
    nth_error (combine l1 l2) n = Some (x, y).
Proof.
  intros A B l1. induction l1 as [| a l1' IH]; intros l2 n x y H1 H2;
    destruct l2 as [| b l2']; destruct n as [| n']; cbn in *;
    try discriminate.
  - injection H1 as <-. injection H2 as <-. reflexivity.
  - exact (IH l2' n' x y H1 H2).
Qed.

Theorem canonical_level_increases :
  forall FRs FWs i j FWi FRj,
    length FRs = length FWs ->
    i < j -> j < length FRs ->
    nth_error FWs i = Some FWi ->
    nth_error FRs j = Some FRj ->
    inter FWi FRj = true ->
    Lcan FRs FWs i < Lcan FRs FWs j.
Proof.
  intros FRs FWs i j FWi FRj Hlen Hij Hj HFWi HFRj Hint.
  assert (HFRi : exists FRi, nth_error FRs i = Some FRi).
  { destruct (nth_error FRs i) eqn:E; [eauto |].
    apply nth_error_None in E. lia. }
  destruct HFRi as [FRi HFRi].
  assert (HFWj : exists FWj, nth_error FWs j = Some FWj).
  { destruct (nth_error FWs j) eqn:E; [eauto |].
    apply nth_error_None in E. rewrite <- Hlen in E. lia. }
  destruct HFWj as [FWj HFWj].
  pose proof (nth_error_combine _ _ FRs FWs i FRi FWi HFRi HFWi) as Hci.
  pose proof (nth_error_combine _ _ FRs FWs j FRj FWj HFRj HFWj) as Hcj.
  assert (Hlc : length (levels FRs FWs) = length (combine FRs FWs))
    by (unfold levels; apply levels_go_len).
  assert (Hjc : j < length (combine FRs FWs)).
  { apply nth_error_Some. rewrite Hcj. discriminate. }
  assert (Hic : i < length (combine FRs FWs)) by lia.
  unfold Lcan.
  assert (HLi : nth_error (levels FRs FWs) i
                = Some (nth i (levels FRs FWs) 0)).
  { apply nth_error_nth'. lia. }
  assert (HLj : nth_error (levels FRs FWs) j
                = Some (nth j (levels FRs FWs) 0)).
  { apply nth_error_nth'. lia. }
  exact (levels_go_spec (combine FRs FWs) [] i j FRi FWi FRj FWj
           (nth i (levels FRs FWs) 0) (nth j (levels FRs FWs) 0)
           Hij Hci Hcj HLi HLj Hint).
Qed.

Corollary canonical_rounds_converge :
  forall (ts : list item) (FRs FWs : list (list key)) (cok : addr -> Prop)
         (r : nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j fee non t g p FR FW,
        nth_error ts j = Some (fee, non, t, g, p) ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW ->
        fp FR FW [] [] [] cok fee t /\ code_certified FR FW [] [] [] cok) ->
    (forall j, j < length ts -> Lcan FRs FWs j <= S r) ->
    snd (omerge (st, bk, nm) ts
          (map (fun j => (of_state (mvstor (st, bk, nm) ts
                            (fun i => Lcan FRs FWs i <=? r) j),
                          of_bank bk, of_nonces nm))
               (seq 0 (length ts)))) = 0.
Proof.
  intros ts FRs FWs cok r st bk nm HlenR HlenW Hcert Hmax.
  apply (level_rounds_converge ts FRs FWs cok (Lcan FRs FWs) r);
    try assumption.
  intros i j FWi FRj Hij Hj HFWi HFRj Hint.
  apply (canonical_level_increases FRs FWs i j FWi FRj);
    try assumption; lia.
Qed.

(** ** The operational concurrent scheduler

    Workers over a multi-version store under an explicit interleaving
    semantics.  A state carries the committed prefix length, the committed
    machine, the committed receipts, per-position incarnation counters,
    the executed-but-uncommitted outcomes with the version stamps they
    read under, the version stamps of the committed storage, and the
    commit-time re-execution count.  [AExec j] runs position [j] against
    the store of the moment: committed storage overlaid, in index order,
    with the write buffers of executed lower positions, and the committed
    bank and nonces advanced by the recorded effects of executed lower
    positions.  [AVal j] eagerly validates an uncommitted position's
    version stamps against the store of the moment and aborts it on
    disagreement, bumping its incarnation.  [ACommit] drives the commit
    wavefront: version agreement commits the head's outcome with no value
    re-read of storage, value agreement commits it through the shared
    [cstep], disagreement re-executes it there, and an unfunded or
    misnonced transaction is rejected without running. *)

Definition stampeqb (a b : option (nat * nat)) : bool :=
  match a, b with
  | None, None => true
  | Some (i1, n1), Some (i2, n2) => (i1 =? i2) && (n1 =? n2)
  | _, _ => false
  end.

Lemma stampeqb_eq : forall a b, stampeqb a b = true -> a = b.
Proof.
  intros [[i1 n1] |] [[i2 n2] |] H; cbn in H; try discriminate.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
  - reflexivity.
Qed.

Definition vercheck (slog : list (key * val))
           (vs now : key -> option (nat * nat)) : bool :=
  forallb (fun kv => stampeqb (vs (fst kv)) (now (fst kv))) slog.

Lemma vercheck_In :
  forall slog vs now,
    vercheck slog vs now = true ->
    forall k v, In (k, v) slog -> vs k = now k.
Proof.
  intros slog vs now Hv k v Hin.
  unfold vercheck in Hv. rewrite forallb_forall in Hv.
  apply stampeqb_eq. exact (Hv (k, v) Hin).
Qed.

Lemma in_fst_wlookup :
  forall w k, In k (map fst w) -> exists v, wlookup w k = Some v.
Proof.
  induction w as [| [k0 v0] r IH]; cbn; intros k Hin; [contradiction |].
  destruct (keqb k k0) eqn:He; [eauto |].
  destruct Hin as [-> | Hin].
  - rewrite keqb_refl in He. discriminate.
  - exact (IH k Hin).
Qed.

Record ostate : Type := OSt {
  os_c   : nat;
  os_m   : mach;
  os_rs  : list rcpt;
  os_inc : nat -> nat;
  os_out : nat -> option (out * (key -> option (nat * nat)));
  os_stamp : key -> option (nat * nat);
  os_rx  : nat
}.

Definition obuf (s : ostate) (i : nat) : buffer :=
  match os_out s i with
  | Some (o, _) => if o_ok o then o_buf o else []
  | None => []
  end.

Fixpoint ostor_go (base : storage) (ob : nat -> buffer)
         (from cnt : nat) : storage :=
  match cnt with
  | 0 => base
  | S c => ostor_go (commit base (ob from)) ob (S from) c
  end.

Definition ostor (s : ostate) (j : nat) : storage :=
  ostor_go (fst (fst (os_m s))) (obuf s) (os_c s) (j - os_c s).

Definition stamp1 (s : ostate) (i : nat)
           (base : key -> option (nat * nat)) : key -> option (nat * nat) :=
  fun k => if inkey k (map fst (obuf s i)) then Some (i, os_inc s i)
           else base k.

Fixpoint ostamp_go (s : ostate) (base : key -> option (nat * nat))
         (from cnt : nat) : key -> option (nat * nat) :=
  match cnt with
  | 0 => base
  | S c => ostamp_go s (stamp1 s from base) (S from) c
  end.

Definition ostamp (s : ostate) (j : nat) : key -> option (nat * nat) :=
  ostamp_go s (os_stamp s) (os_c s) (j - os_c s).

Definition beff (i : item) (o : out) (bknm : bank * nonces)
  : bank * nonces :=
  let '(bk, nm) := bknm in
  let '(fee, non, t, g, p) := i in
  if gateb bk nm i
  then
    let u := g - o_gas o in
    if o_ok o
    then
      let u_eff := u - Nat.min (o_ref o) (u / 2) in
      let b1 := bupd bk fee (bk fee - g * (BF + p)) in
      let b2 := apply_tvs b1 (o_tvs o) in
      let b3 := bupd b2 fee (b2 fee + (g - u_eff) * (BF + p)) in
      (bupd b3 CB (b3 CB + u_eff * p), bupd nm fee (S (nm fee)))
    else
      (bupd (bupd bk fee (bk fee - u * (BF + p))) CB
            (bupd bk fee (bk fee - u * (BF + p)) CB + u * p),
       bupd nm fee (S (nm fee)))
  else (bk, nm).

Fixpoint obknm_go (ts : list item) (s : ostate) (bknm : bank * nonces)
         (from cnt : nat) : bank * nonces :=
  match cnt with
  | 0 => bknm
  | S c =>
      obknm_go ts s
        (match os_out s from with
         | Some (o, _) => beff (nth from ts ditem) o bknm
         | None => bknm
         end)
        (S from) c
  end.

Definition obknm (ts : list item) (s : ostate) (j : nat) : bank * nonces :=
  obknm_go ts s (snd (fst (os_m s)), snd (os_m s)) (os_c s) (j - os_c s).

Definition cstamp (h inc : nat) (w : buffer)
           (base : key -> option (nat * nat)) : key -> option (nat * nat) :=
  fun k => if inkey k (map fst w) then Some (h, inc) else base k.

Inductive oact : Type :=
| AExec (j : nat)
| AVal (j : nat)
| ACommit.

Definition ostep (ts : list item) (s : ostate) (a : oact) : ostate :=
  match a with
  | AExec j =>
      if (os_c s <=? j) && (j <? length ts)
      then match nth_error ts j with
           | Some i =>
               let o := runt i (of_state (ostor s j))
                             (of_bank (fst (obknm ts s j)))
                             (of_nonces (snd (obknm ts s j))) in
               OSt (os_c s) (os_m s) (os_rs s)
                   (fun j' => if j' =? j then S (os_inc s j')
                              else os_inc s j')
                   (fun j' => if j' =? j then Some (o, ostamp s j)
                              else os_out s j')
                   (os_stamp s) (os_rx s)
           | None => s
           end
      else s
  | AVal j =>
      if (os_c s <=? j) && (j <? length ts)
      then match os_out s j with
           | Some (o, vs) =>
               if vercheck (o_slog o) vs (ostamp s j)
               then s
               else OSt (os_c s) (os_m s) (os_rs s)
                        (fun j' => if j' =? j then S (os_inc s j')
                                   else os_inc s j')
                        (fun j' => if j' =? j then None else os_out s j')
                        (os_stamp s) (os_rx s)
           | None => s
           end
      else s
  | ACommit =>
      if os_c s <? length ts
      then match nth_error ts (os_c s) with
           | Some i =>
               let '(st, bk, nm) := os_m s in
               match os_out s (os_c s) with
               | Some (o, vs) =>
                   if vercheck (o_slog o) vs (os_stamp s)
                      && bvalid bk (o_blog o) && nvalid nm (o_nlog o)
                      && gateb bk nm i
                   then
                     let '(fee, non, t, g, p) := i in
                     let '(m1, r) := finish st bk nm fee g p o in
                     OSt (S (os_c s)) m1 (os_rs s ++ [r]) (os_inc s)
                         (os_out s)
                         (cstamp (os_c s) (os_inc s (os_c s))
                                 (if o_ok o then o_buf o else [])
                                 (os_stamp s))
                         (os_rx s)
                   else if gateb bk nm i
                   then
                     let '(mr, fl) := cstep (os_m s) i (Some o) in
                     let '(m1, r) := mr in
                     if fl
                     then
                       let o' := runt i (of_state st) (of_bank bk)
                                      (of_nonces nm) in
                       OSt (S (os_c s)) m1 (os_rs s ++ [r])
                           (fun j' => if j' =? os_c s
                                      then S (os_inc s j')
                                      else os_inc s j')
                           (fun j' => if j' =? os_c s
                                      then Some (o', os_stamp s)
                                      else os_out s j')
                           (cstamp (os_c s) (S (os_inc s (os_c s)))
                                   (if o_ok o' then o_buf o' else [])
                                   (os_stamp s))
                           (S (os_rx s))
                     else
                       OSt (S (os_c s)) m1 (os_rs s ++ [r]) (os_inc s)
                           (os_out s)
                           (cstamp (os_c s) (os_inc s (os_c s))
                                   (if o_ok o then o_buf o else [])
                                   (os_stamp s))
                           (os_rx s)
                   else
                     OSt (S (os_c s)) (os_m s) (os_rs s ++ [rejrcpt])
                         (os_inc s) (os_out s) (os_stamp s) (os_rx s)
               | None =>
                   if gateb bk nm i
                   then
                     let '(mr, fl) := cstep (os_m s) i None in
                     let '(m1, r) := mr in
                     let o' := runt i (of_state st) (of_bank bk)
                                    (of_nonces nm) in
                     OSt (S (os_c s)) m1 (os_rs s ++ [r])
                         (fun j' => if j' =? os_c s
                                    then S (os_inc s j') else os_inc s j')
                         (fun j' => if j' =? os_c s
                                    then Some (o', os_stamp s)
                                    else os_out s j')
                         (cstamp (os_c s) (S (os_inc s (os_c s)))
                                 (if o_ok o' then o_buf o' else [])
                                 (os_stamp s))
                         (os_rx s)
                   else
                     OSt (S (os_c s)) (os_m s) (os_rs s ++ [rejrcpt])
                         (os_inc s) (os_out s) (os_stamp s) (os_rx s)
               end
           | None => s
           end
      else s
  end.

Definition oinit (m0 : mach) : ostate :=
  OSt 0 m0 [] (fun _ => 0) (fun _ => None) (fun _ => None) 0.

Definition reach (ts : list item) (s0 : ostate) (acts : list oact) : ostate :=
  fold_left (ostep ts) acts s0.

Lemma reach_app :
  forall ts s l1 l2, reach ts s (l1 ++ l2) = reach ts (reach ts s l1) l2.
Proof.
  intros ts s l1 l2. unfold reach. apply fold_left_app.
Qed.

Lemma seq_rcpt_nth :
  forall ts m j,
    j < length ts ->
    nth_error (snd (seq_execr m ts)) j
    = Some (snd (step (mach_at m ts j) (nth j ts ditem))).
Proof.
  induction ts as [| i rest IH]; intros m j Hj; cbn in Hj; [lia |].
  cbn [seq_execr].
  destruct (step m i) as [m1 r] eqn:ES.
  destruct (seq_execr m1 rest) as [m2 rs] eqn:E.
  destruct j as [| j'].
  - cbn. rewrite ES. reflexivity.
  - cbn [snd nth_error mach_at nth].
    assert (HI := IH m1 j' ltac:(lia)). rewrite E in HI. cbn [snd] in HI.
    rewrite ES. cbn [fst]. exact HI.
Qed.

Lemma mach_at_full :
  forall ts m, mach_at m ts (length ts) = fst (seq_execr m ts).
Proof.
  induction ts as [| i rest IH]; intros m; cbn [length seq_execr mach_at].
  - reflexivity.
  - destruct (step m i) as [m1 r] eqn:ES.
    destruct (seq_execr m1 rest) as [m2 rs] eqn:E.
    assert (HI := IH m1). rewrite E in HI. cbn [fst] in HI.
    cbn [fst]. exact HI.
Qed.

Lemma firstn_succ_nth :
  forall (A : Type) (l : list A) (c : nat) (d : A),
    c < length l ->
    firstn (S c) l = firstn c l ++ [nth c l d].
Proof.
  intros A l. induction l as [| x l' IH]; intros c d Hc; cbn in Hc; [lia |].
  destruct c as [| c']; cbn [firstn nth].
  - reflexivity.
  - cbn [app]. f_equal. apply IH. lia.
Qed.

(** The stamp semantics: a captured stamp names the writer whose buffer
    holds the value read, guarded by the writer's incarnation; a missing
    stamp names the committed storage, guarded by the key still being
    unstamped. *)

Definition stampw (s : ostate) (k : key) (vv : val)
           (st0 : option (nat * nat)) : Prop :=
  match st0 with
  | Some (i2, inc2) =>
      os_inc s i2 = inc2 ->
      exists o2 vs2, os_out s i2 = Some (o2, vs2)
        /\ o_ok o2 = true /\ wlookup (o_buf o2) k = Some vv
  | None => os_stamp s k = None -> fst (fst (os_m s)) k = vv
  end.

Definition oinv (m0 : mach) (ts : list item) (s : ostate) : Prop :=
  os_c s <= length ts
  /\ os_m s = mach_at m0 ts (os_c s)
  /\ os_rs s = firstn (os_c s) (snd (seq_execr m0 ts))
  /\ (forall j o vs, os_out s j = Some (o, vs) ->
        (exists rd brd nrd i,
            nth_error ts j = Some i /\ o = runt i rd brd nrd)
        /\ (forall k v, In (k, v) (o_slog o) -> stampw s k v (vs k))
        /\ (forall k i2 inc2, vs k = Some (i2, inc2) ->
              inc2 <= os_inc s i2))
  /\ (forall k i2 inc2, os_stamp s k = Some (i2, inc2) ->
        i2 < os_c s /\ os_inc s i2 = inc2
        /\ exists o2 vs2, os_out s i2 = Some (o2, vs2)
             /\ o_ok o2 = true
             /\ wlookup (o_buf o2) k = Some (fst (fst (os_m s)) k)).

(** Version agreement implies value agreement: a slog entry whose captured
    stamp equals the committed stamp reads, through the shared immutable
    incarnation, the very buffer value the committed storage holds. *)

Lemma vercheck_valid :
  forall s (slog : list (key * val)) (vs : key -> option (nat * nat)),
    (forall k v, In (k, v) slog -> stampw s k v (vs k)) ->
    (forall k i2 inc2, os_stamp s k = Some (i2, inc2) ->
        i2 < os_c s /\ os_inc s i2 = inc2
        /\ exists o2 vs2, os_out s i2 = Some (o2, vs2)
             /\ o_ok o2 = true
             /\ wlookup (o_buf o2) k = Some (fst (fst (os_m s)) k)) ->
    vercheck slog vs (os_stamp s) = true ->
    valid (fst (fst (os_m s))) slog = true.
Proof.
  intros s slog vs Hw Hb Hv.
  induction slog as [| [k v] rest IH]; [reflexivity |].
  cbn [vercheck forallb] in Hv. apply andb_true_iff in Hv.
  destruct Hv as [Hh Hv].
  cbn [valid]. apply andb_true_iff. split.
  - apply stampeqb_eq in Hh. cbn [fst] in Hh.
    pose proof (Hw k v (or_introl eq_refl)) as Hwk.
    destruct (os_stamp s k) as [[i2 inc2] |] eqn:Hsk.
    + rewrite Hh in Hwk. cbn [stampw] in Hwk.
      destruct (Hb k i2 inc2 Hsk) as (Hlt & Hinc & o2 & vs2 & Ho2 & Hok
                                      & Hlk).
      destruct (Hwk Hinc) as (o2' & vs2' & Ho2' & Hok' & Hlk').
      rewrite Ho2 in Ho2'. injection Ho2' as <- <-.
      rewrite Hlk in Hlk'. injection Hlk' as ->.
      apply Nat.eqb_refl.
    + rewrite Hh in Hwk. cbn [stampw] in Hwk.
      rewrite (Hwk Hsk). apply Nat.eqb_refl.
  - apply IH; [| exact Hv].
    intros k0 v0 Hin. apply Hw. right. exact Hin.
Qed.

(** Capture consistency: the stamps the overlay presents at execution time
    witness exactly the values the overlay serves. *)

Lemma obuf_decode :
  forall s i k,
    In k (map fst (obuf s i)) ->
    exists o vs, os_out s i = Some (o, vs) /\ o_ok o = true
      /\ obuf s i = o_buf o.
Proof.
  intros s i k Hin. unfold obuf in *.
  destruct (os_out s i) as [[o vs] |] eqn:E; [| destruct Hin].
  destruct (o_ok o) eqn:Hok; [| destruct Hin].
  exists o, vs. auto.
Qed.

Lemma sync_go :
  forall s cnt from (base : storage)
         (bstamp : key -> option (nat * nat)),
    (forall k, stampw s k (base k) (bstamp k)) ->
    forall k, stampw s k (ostor_go base (obuf s) from cnt k)
                     (ostamp_go s bstamp from cnt k).
Proof.
  intros s cnt. induction cnt as [| c IH]; intros from base bstamp Hs k.
  - exact (Hs k).
  - cbn [ostor_go ostamp_go].
    apply IH.
    intros k0. unfold stamp1.
    destruct (inkey k0 (map fst (obuf s from))) eqn:Hk0.
    + apply inkey_in in Hk0.
      destruct (obuf_decode s from k0 Hk0) as (o2 & vs2 & Ho2 & Hok & Hb).
      cbn [stampw]. intros _.
      exists o2, vs2. split; [exact Ho2 |]. split; [exact Hok |].
      rewrite Hb in Hk0.
      destruct (in_fst_wlookup (o_buf o2) k0 Hk0) as [v0 Hv0].
      rewrite (commit_wlookup (obuf s from) base k0 v0)
        by (rewrite Hb; exact Hv0).
      exact Hv0.
    + assert (Hct : commit base (obuf s from) k0 = base k0).
      { apply commit_untouched. intro Hx. apply inkey_in in Hx.
        congruence. }
      rewrite Hct. exact (Hs k0).
Qed.

Lemma ostamp_go_lt :
  forall s cnt from (bstamp : key -> option (nat * nat)),
    (forall k i2 inc2, bstamp k = Some (i2, inc2) -> i2 < from) ->
    forall k i2 inc2,
      ostamp_go s bstamp from cnt k = Some (i2, inc2) -> i2 < from + cnt.
Proof.
  intros s cnt. induction cnt as [| c IH]; intros from bstamp Hb k i2 inc2 H.
  - cbn in H. specialize (Hb k i2 inc2 H). lia.
  - cbn [ostamp_go] in H.
    assert (Hb' : forall k0 i0 n0,
               stamp1 s from bstamp k0 = Some (i0, n0) -> i0 < S from).
    { intros k0 i0 n0 Hs1. unfold stamp1 in Hs1.
      destruct (inkey k0 (map fst (obuf s from))).
      - injection Hs1 as <- <-. lia.
      - specialize (Hb k0 i0 n0 Hs1). lia. }
    pose proof (IH (S from) (stamp1 s from bstamp) Hb' k i2 inc2 H). lia.
Qed.

Lemma ostamp_go_bound :
  forall s cnt from (bstamp : key -> option (nat * nat)),
    (forall k i2 inc2, bstamp k = Some (i2, inc2) -> inc2 <= os_inc s i2) ->
    forall k i2 inc2,
      ostamp_go s bstamp from cnt k = Some (i2, inc2) ->
      inc2 <= os_inc s i2.
Proof.
  intros s cnt. induction cnt as [| c IH]; intros from bstamp Hb k i2 inc2 H.
  - exact (Hb k i2 inc2 H).
  - cbn [ostamp_go] in H.
    assert (Hb' : forall k0 i0 n0,
               stamp1 s from bstamp k0 = Some (i0, n0) ->
               n0 <= os_inc s i0).
    { intros k0 i0 n0 Hs1. unfold stamp1 in Hs1.
      destruct (inkey k0 (map fst (obuf s from))).
      - injection Hs1 as <- <-. lia.
      - exact (Hb k0 i0 n0 Hs1). }
    exact (IH (S from) (stamp1 s from bstamp) Hb' k i2 inc2 H).
Qed.

Lemma stamp_base_w :
  forall s,
    (forall k i2 inc2, os_stamp s k = Some (i2, inc2) ->
        i2 < os_c s /\ os_inc s i2 = inc2
        /\ exists o2 vs2, os_out s i2 = Some (o2, vs2)
             /\ o_ok o2 = true
             /\ wlookup (o_buf o2) k = Some (fst (fst (os_m s)) k)) ->
    forall k, stampw s k (fst (fst (os_m s)) k) (os_stamp s k).
Proof.
  intros s Hstamp k.
  destruct (os_stamp s k) as [[i2 inc2] |] eqn:Hsk.
  - cbn [stampw]. intros _.
    destruct (Hstamp k i2 inc2 Hsk)
      as (Hlt & Hinc & o2 & vs2 & Ho2 & Hok2 & Hlk2).
    exists o2, vs2. auto.
  - cbn [stampw]. intros _. reflexivity.
Qed.

Lemma ostep_inv :
  forall ts m0 s a, oinv m0 ts s -> oinv m0 ts (ostep ts s a).
Proof.
  intros ts m0 s a Hinv.
  pose proof Hinv as [Hc [Hm [Hr [Hout Hstamp]]]].
  assert (Hbnd0 : forall k0 i0 n0,
             os_stamp s k0 = Some (i0, n0) -> n0 <= os_inc s i0).
  { intros k0 i0 n0 Hs0.
    destruct (Hstamp k0 i0 n0 Hs0) as (_ & Hinc0 & _). lia. }
  assert (Hlt0 : forall k0 i0 n0,
             os_stamp s k0 = Some (i0, n0) -> i0 < os_c s).
  { intros k0 i0 n0 Hs0.
    destruct (Hstamp k0 i0 n0 Hs0) as (Hl & _). exact Hl. }
  destruct a as [j | j |].
  - (* AExec *)
    cbn [ostep].
    destruct ((os_c s <=? j) && (j <? length ts)) eqn:Hgj;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    apply andb_true_iff in Hgj. destruct Hgj as [Hgj1 Hgj2].
    apply Nat.leb_le in Hgj1. apply Nat.ltb_lt in Hgj2.
    destruct (nth_error ts j) as [i |] eqn:Hij;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
    split; [exact Hc |]. split; [exact Hm |]. split; [exact Hr |].
    split.
    + intros j0 o0 vs0 Ho0. cbn [os_out] in Ho0.
      destruct (j0 =? j) eqn:Hjj.
      * apply Nat.eqb_eq in Hjj. subst j0.
        injection Ho0 as <- <-.
        split; [| split].
        -- exists (of_state (ostor s j)), (of_bank (fst (obknm ts s j))),
                  (of_nonces (snd (obknm ts s j))), i.
           split; [exact Hij | reflexivity].
        -- intros k v Hin.
           assert (Hv : ostor s j k = v).
           { refine (valid_true_In _ (ostor s j) _ k v Hin).
             unfold runt. destruct i as [[[[fee non] t] g] p].
             cbv beta iota zeta.
             apply valid_self_s. }
           subst v.
           pose proof (sync_go s (j - os_c s) (os_c s)
                         (fst (fst (os_m s))) (os_stamp s)
                         (stamp_base_w s Hstamp) k) as Hsy.
           pose proof (ostamp_go_bound s (j - os_c s) (os_c s) (os_stamp s)
                         Hbnd0) as Hbnd.
           pose proof (ostamp_go_lt s (j - os_c s) (os_c s) (os_stamp s)
                         Hlt0) as Hltl.
           unfold ostamp, ostor in *.
           destruct (ostamp_go s (os_stamp s) (os_c s) (j - os_c s) k)
             as [[i2 inc2] |] eqn:Hcap.
           ++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hsy |- *.
              intros Hginc.
              assert (Hi2j : i2 < os_c s + (j - os_c s))
                by (exact (Hltl k i2 inc2 Hcap)).
              assert (Hne : i2 <> j) by lia.
              apply Nat.eqb_neq in Hne.
              rewrite Hne in Hginc.
              destruct (Hsy Hginc) as (o2 & vs2 & Ho2 & Hok2 & Hlk2).
              exists o2, vs2. try rewrite Hne. auto.
           ++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hsy |- *.
              intros Hnone. exact (Hsy Hnone).
        -- intros k i2 inc2 Hcap.
           unfold ostamp in Hcap.
           pose proof (ostamp_go_bound s (j - os_c s) (os_c s) (os_stamp s)
                         Hbnd0 k i2 inc2 Hcap) as Hbnd.
           pose proof (ostamp_go_lt s (j - os_c s) (os_c s) (os_stamp s)
                         Hlt0 k i2 inc2 Hcap) as Hltl.
           assert (Hne : i2 <> j) by lia.
           apply Nat.eqb_neq in Hne. cbn [os_inc]. rewrite Hne. exact Hbnd.
      * destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
        split; [exact Hprov |]. split.
        -- intros k v Hin.
           pose proof (Hw k v Hin) as Hwk.
           destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
           ++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
              intros Hginc.
              destruct (i2 =? j) eqn:He2.
              ** cbn in Hginc.
                 pose proof (Hb k i2 inc2 Hvk) as Hle2.
                 exfalso. lia.
              ** destruct (Hwk Hginc) as (o2 & vs2 & Ho2 & Hok2 & Hlk2).
                 exists o2, vs2. cbn. auto.
           ++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
        -- intros k i2 inc2 Hvk.
           pose proof (Hb k i2 inc2 Hvk) as Hle2.
           cbn [os_inc]. destruct (i2 =? j) eqn:He2; cbn; lia.
    + intros k i2 inc2 Hsk.
      cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
      destruct (Hstamp k i2 inc2 Hsk)
        as (Hlt & Hinc & o2 & vs2 & Ho2 & Hok2 & Hlk2).
      assert (Hne : i2 <> j) by lia.
      apply Nat.eqb_neq in Hne.
      split; [exact Hlt |]. split; [rewrite Hne; exact Hinc |].
      exists o2, vs2. try rewrite Hne. auto.
  - (* AVal *)
    cbn [ostep].
    destruct ((os_c s <=? j) && (j <? length ts)) eqn:Hgj;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    apply andb_true_iff in Hgj. destruct Hgj as [Hgj1 Hgj2].
    apply Nat.leb_le in Hgj1. apply Nat.ltb_lt in Hgj2.
    destruct (os_out s j) as [[o vs] |] eqn:Hoj;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    destruct (vercheck (o_slog o) vs (ostamp s j)) eqn:Hvc;
      [exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp)))) |].
    cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
    split; [exact Hc |]. split; [exact Hm |]. split; [exact Hr |].
    split.
    + intros j0 o0 vs0 Ho0. cbn [os_out] in Ho0.
      destruct (j0 =? j) eqn:Hjj; [discriminate |].
      destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
      split; [exact Hprov |]. split.
      * intros k v Hin.
        pose proof (Hw k v Hin) as Hwk.
        destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
        -- cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
           intros Hginc.
           destruct (i2 =? j) eqn:He2.
           ++ cbn in Hginc.
              pose proof (Hb k i2 inc2 Hvk) as Hle2.
              exfalso. lia.
           ++ destruct (Hwk Hginc) as (o2 & vs2 & Ho2 & Hok2 & Hlk2).
              exists o2, vs2. cbn. auto.
        -- cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
      * intros k i2 inc2 Hvk.
        pose proof (Hb k i2 inc2 Hvk) as Hle2.
        cbn [os_inc]. destruct (i2 =? j) eqn:He2; cbn; lia.
    + intros k i2 inc2 Hsk.
      cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
      destruct (Hstamp k i2 inc2 Hsk)
        as (Hlt & Hinc & o2 & vs2 & Ho2 & Hok2 & Hlk2).
      assert (Hne : i2 <> j) by lia.
      apply Nat.eqb_neq in Hne.
      split; [exact Hlt |]. split; [rewrite Hne; exact Hinc |].
      exists o2, vs2. try rewrite Hne. auto.
  - (* ACommit *)
    cbn [ostep].
    destruct (os_c s <? length ts) eqn:Hlt;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    apply Nat.ltb_lt in Hlt.
    destruct (nth_error ts (os_c s)) as [i |] eqn:Hi;
      [| exact (conj Hc (conj Hm (conj Hr (conj Hout Hstamp))))].
    assert (Hnth : @nth item (os_c s) ts ditem = i)
      by (apply nth_error_nth; exact Hi).
    assert (Hrs' : forall r,
               r = snd (step (mach_at m0 ts (os_c s)) i) ->
               os_rs s ++ [r]
               = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
    { intros r Hrr.
      rewrite (firstn_succ_nth rcpt (snd (seq_execr m0 ts)) (os_c s)
                 rejrcpt).
      2:{ rewrite seq_rcpt_len. exact Hlt. }
      rewrite Hr. f_equal. f_equal.
      assert (Hn := seq_rcpt_nth ts m0 (os_c s) Hlt).
      rewrite Hnth in Hn.
      assert (Hn2 : nth (os_c s) (snd (seq_execr m0 ts)) rejrcpt
                    = snd (step (mach_at m0 ts (os_c s)) i))
        by (apply nth_error_nth; exact Hn).
      rewrite Hn2. rewrite Hrr. reflexivity. }
    assert (Hma : forall m1,
               m1 = fst (step (mach_at m0 ts (os_c s)) i) ->
               m1 = mach_at m0 ts (S (os_c s))).
    { intros m1 Hm1.
      rewrite (mach_at_S ts m0 (os_c s) Hlt). rewrite Hnth. exact Hm1. }
    destruct (os_m s) as [[st bk] nm] eqn:EOM.
    assert (Hstq : mach_at m0 ts (os_c s) = (st, bk, nm))
      by (symmetry; exact Hm).
    destruct i as [[[[fee non] t] g] p].
    destruct (os_out s (os_c s)) as [[o vs] |] eqn:Hoc.
    + (* an outcome is present *)
      destruct (Hout (os_c s) o vs Hoc) as (HprovH & HwH & HbH).
      destruct (vercheck (o_slog o) vs (os_stamp s)
                && bvalid bk (o_blog o) && nvalid nm (o_nlog o)
                && gateb bk nm (fee, non, t, g, p)) eqn:HA.
      * (* version-validated commit *)
        apply andb_true_iff in HA. destruct HA as [HA Hg].
        apply andb_true_iff in HA. destruct HA as [HA Hvn].
        apply andb_true_iff in HA. destruct HA as [Hvv Hvb].
        assert (Evs : valid st (o_slog o) = true).
        { assert (Hst' : fst (fst (os_m s)) = st) by (rewrite EOM; reflexivity).
          rewrite <- Hst'.
          apply (vercheck_valid s (o_slog o) vs); [exact HwH | | exact Hvv].
          intros k0 i0 n0 Hs0.
          destruct (Hstamp k0 i0 n0 Hs0)
            as (Hl0 & Hinc0 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
          split; [exact Hl0 |]. split; [exact Hinc0 |].
          exists o2, vs2. rewrite EOM. auto. }
        assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                        = finish st bk nm fee g p o).
        { destruct HprovH as (rd0 & brd0 & nrd0 & i' & Hi' & Ho').
          rewrite Hi in Hi'. injection Hi' as <-.
          subst o.
          unfold step. rewrite Hg.
          rewrite (replay_runt (fee, non, t, g, p) rd0 brd0 nrd0 st bk nm
                     Evs Hvb Hvn).
          reflexivity. }
        destruct (finish st bk nm fee g p o) as [m1 r] eqn:EF.
        cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
        assert (Hm1 : m1 = mach_at m0 ts (S (os_c s))).
        { apply Hma. rewrite Hstq. rewrite Hstep. reflexivity. }
        assert (Hr1 : os_rs s ++ [r]
                      = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
        { apply Hrs'. rewrite Hstq. rewrite Hstep. reflexivity. }
        (* committed storage form *)
        assert (Hm1st : fst (fst m1)
                        = commit st (if o_ok o then o_buf o else [])).
        { unfold finish in EF. cbv zeta in EF.
          destruct (o_ok o) eqn:Hok; cbv beta iota in EF;
            injection EF as E1 E2; rewrite <- E1; reflexivity. }
        split; [exact Hlt |]. split; [exact Hm1 |]. split; [exact Hr1 |].
        split.
        -- intros j0 o0 vs0 Ho0.
           destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
           split; [exact Hprov |]. split.
           ++ intros k v Hin.
              pose proof (Hw k v Hin) as Hwk.
              destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
              ** cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
              ** cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                 intros Hnone. unfold cstamp in Hnone.
                 match type of Hnone with
                 | (if ?b then _ else _) = _ =>
                     destruct b eqn:Hik; try rewrite Hik in Hnone
                 end; [cbn in Hnone; discriminate |].
                 assert (Hik' : inkey k
                            (map fst (if o_ok o then o_buf o else []))
                          = false) by exact Hik.
                 clear Hik. rename Hik' into Hik.
                 rewrite Hm1st.
                 rewrite commit_untouched
                   by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                 try rewrite EOM in Hwk. cbn [fst] in Hwk.
                 exact (Hwk Hnone).
           ++ intros k i2 inc2 Hvk. exact (Hb k i2 inc2 Hvk).
        -- intros k i2 inc2 Hsk. cbn [os_stamp] in Hsk. unfold cstamp in Hsk.
           cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
           match type of Hsk with
           | (if ?b then _ else _) = _ =>
               destruct b eqn:Hik; try rewrite Hik in Hsk
           end;
           [| assert (Hik' : inkey k
                         (map fst (if o_ok o then o_buf o else []))
                       = false) by exact Hik;
              clear Hik; rename Hik' into Hik].
           ++ cbn in Hsk. injection Hsk as <- <-.
              destruct (o_ok o) eqn:Hok; [| try rewrite Hok in Hik; cbn in Hik; discriminate].
              try rewrite Hok in Hik. cbn in Hik.
              apply inkey_in in Hik.
              destruct (in_fst_wlookup (o_buf o) k Hik) as [v0 Hv0].
              split; [lia |]. split; [reflexivity |].
              exists o, vs. split; [exact Hoc |]. split; [exact Hok |].
              try rewrite Hok in Hm1st. cbv beta iota in Hm1st. rewrite Hm1st.
              rewrite (commit_wlookup (o_buf o) st k v0 Hv0).
              exact Hv0.
           ++ destruct (Hstamp k i2 inc2 Hsk)
                as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
              split; [lia |]. split; [exact Hinc2 |].
              exists o2, vs2. split; [exact Ho2 |]. split; [exact Hok2 |].
              rewrite Hm1st.
              rewrite commit_untouched
                by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
              try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
              exact Hlk2.
      * (* value path through the shared step *)
        destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hg.
        -- destruct (cstep (st, bk, nm) (fee, non, t, g, p) (Some o))
             as [[m1 r] fl] eqn:EC.
           unfold cstep in EC. rewrite Hg in EC.
           destruct (vcheck st bk nm o) eqn:Hvchk.
           ++ (* value-validated *)
              injection EC as EC1 EC2. subst fl.
              assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                              = finish st bk nm fee g p o).
              { destruct HprovH as (rd0 & brd0 & nrd0 & i' & Hi' & Ho').
                rewrite Hi in Hi'. injection Hi' as <-.
                subst o.
                unfold vcheck in Hvchk.
                apply andb_true_iff in Hvchk. destruct Hvchk as [Hv1 Hv3].
                apply andb_true_iff in Hv1. destruct Hv1 as [Hv1 Hv2].
                unfold step. rewrite Hg.
                rewrite (replay_runt (fee, non, t, g, p) rd0 brd0 nrd0
                           st bk nm Hv1 Hv2 Hv3).
                reflexivity. }
              cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
              assert (Hm1 : m1 = mach_at m0 ts (S (os_c s))).
              { apply Hma. rewrite Hstq. rewrite Hstep.
                exact (f_equal fst (eq_sym EC1)). }
              assert (Hr1 : os_rs s ++ [r]
                            = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
              { apply Hrs'. rewrite Hstq. rewrite Hstep.
                exact (f_equal snd (eq_sym EC1)). }
              assert (Hm1st : fst (fst m1)
                              = commit st (if o_ok o then o_buf o else [])).
              { unfold finish in EC1. cbv zeta in EC1.
                destruct (o_ok o) eqn:Hok; cbv beta iota in EC1;
                  injection EC1 as E1 E2; rewrite <- E1; reflexivity. }
              split; [exact Hlt |]. split; [exact Hm1 |]. split; [exact Hr1 |].
              split.
              ** intros j0 o0 vs0 Ho0.
                 destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
                 split; [exact Hprov |]. split.
                 --- intros k v Hin.
                     pose proof (Hw k v Hin) as Hwk.
                     destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
                     +++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
                     +++ cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                         intros Hnone. unfold cstamp in Hnone.
                         match type of Hnone with
                         | (if ?b then _ else _) = _ =>
                             destruct b eqn:Hik;
                             try rewrite Hik in Hnone
                         end; [cbn in Hnone; discriminate |].
                         assert (Hik' : inkey k
                                    (map fst (if o_ok o then o_buf o
                                              else []))
                                  = false) by exact Hik.
                         clear Hik. rename Hik' into Hik.
                         rewrite Hm1st.
                         rewrite commit_untouched
                           by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                         try rewrite EOM in Hwk. cbn [fst] in Hwk.
                         exact (Hwk Hnone).
                 --- intros k i2 inc2 Hvk. exact (Hb k i2 inc2 Hvk).
              ** intros k i2 inc2 Hsk. cbn [os_stamp] in Hsk. unfold cstamp in Hsk.
           cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
                 match type of Hsk with
                 | (if ?b then _ else _) = _ =>
                     destruct b eqn:Hik; try rewrite Hik in Hsk
                 end;
                 [| assert (Hik' : inkey k
                               (map fst (if o_ok o then o_buf o else []))
                             = false) by exact Hik;
                    clear Hik; rename Hik' into Hik].
                 --- cbn in Hsk. injection Hsk as <- <-.
                     destruct (o_ok o) eqn:Hok;
                       [| try rewrite Hok in Hik; cbn in Hik; discriminate].
                     try rewrite Hok in Hik. cbn in Hik.
                     apply inkey_in in Hik.
                     destruct (in_fst_wlookup (o_buf o) k Hik) as [v0 Hv0].
                     split; [lia |]. split; [reflexivity |].
                     exists o, vs. split; [exact Hoc |].
                     split; [exact Hok |].
                     try rewrite Hok in Hm1st. cbv beta iota in Hm1st. rewrite Hm1st.
                     rewrite (commit_wlookup (o_buf o) st k v0 Hv0).
                     exact Hv0.
                 --- destruct (Hstamp k i2 inc2 Hsk)
                       as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
                     split; [lia |]. split; [exact Hinc2 |].
                     exists o2, vs2. split; [exact Ho2 |].
                     split; [exact Hok2 |].
                     rewrite Hm1st.
                     rewrite commit_untouched
                       by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                     try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
                     exact Hlk2.
           ++ (* conflicted: re-execute at the head *)
              injection EC as EC1 EC2. subst fl.
              cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
              set (o' := runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                              (of_nonces nm)) in *.
              assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                              = finish st bk nm fee g p o').
              { unfold step. rewrite Hg. reflexivity. }
              assert (Hm1 : m1 = mach_at m0 ts (S (os_c s))).
              { apply Hma. rewrite Hstq.
                exact (f_equal fst (eq_sym EC1)). }
              assert (Hr1 : os_rs s ++ [r]
                            = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
              { apply Hrs'. rewrite Hstq.
                exact (f_equal snd (eq_sym EC1)). }
              assert (Hm1st : fst (fst m1)
                              = commit st (if o_ok o' then o_buf o'
                                           else [])).
              { assert (EC1' : finish st bk nm fee g p o' = (m1, r))
                  by (rewrite <- Hstep; exact EC1).
                unfold finish in EC1'. cbv zeta in EC1'.
                destruct (o_ok o') eqn:Hok; try rewrite Hok in EC1';
                  cbv beta iota in EC1';
                  injection EC1' as E1 E2; rewrite <- E1; reflexivity. }
              split; [exact Hlt |]. split; [exact Hm1 |]. split; [exact Hr1 |].
              split.
              ** intros j0 o0 vs0 Ho0. cbn [os_out] in Ho0.
                 destruct (j0 =? os_c s) eqn:Hjj.
                 --- apply Nat.eqb_eq in Hjj. subst j0.
                     injection Ho0 as <- <-.
                     split; [| split].
                     +++ exists (of_state st), (of_bank bk), (of_nonces nm),
                              (fee, non, t, g, p).
                         split; [exact Hi | reflexivity].
                     +++ intros k v Hin.
                         assert (Hv : st k = v).
                         { refine (valid_true_In _ st _ k v Hin).
                           unfold o', runt. cbv beta iota zeta.
                           apply valid_self_s. }
                         subst v.
                         destruct (os_stamp s k) as [[i2 inc2] |] eqn:Hsk.
                         *** cbn [stampw os_c os_m os_rs os_inc os_out
                                  os_stamp os_rx].
                             intros Hginc.
                             destruct (Hstamp k i2 inc2 Hsk)
                               as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2
                                   & Hlk2).
                             assert (Hne : i2 <> os_c s) by lia.
                             apply Nat.eqb_neq in Hne.
                             exists o2, vs2. try rewrite Hne.
                             split; [exact Ho2 |]. split; [exact Hok2 |].
                             try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
                             exact Hlk2.
                         *** cbn [stampw os_c os_m os_rs os_inc os_out
                                  os_stamp os_rx].
                             intros Hnone. unfold cstamp in Hnone.
                             match type of Hnone with
                             | (if ?b then _ else _) = _ =>
                                 destruct b eqn:Hik;
                                 try rewrite Hik in Hnone
                             end; [cbn in Hnone; discriminate |].
                             assert (Hik' : inkey k
                                        (map fst (if o_ok o' then o_buf o'
                                                  else []))
                                      = false) by exact Hik.
                             clear Hik. rename Hik' into Hik.
                             rewrite Hm1st.
                             rewrite commit_untouched
                               by (intro Hx; apply inkey_in in Hx;
                                   pose proof (eq_trans (eq_sym Hx) Hik)
                                     as E;
                                   discriminate).
                             reflexivity.
                     +++ intros k i2 inc2 Hsk.
                         destruct (Hstamp k i2 inc2 Hsk)
                           as (Hl2 & Hinc2 & _).
                         assert (Hne : i2 <> os_c s) by lia.
                         apply Nat.eqb_neq in Hne. cbn [os_inc os_c]. rewrite Hne. lia.
                 --- destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
                     split; [exact Hprov |]. split.
                     +++ intros k v Hin.
                         pose proof (Hw k v Hin) as Hwk.
                         destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
                         *** cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                             intros Hginc.
                             destruct (i2 =? os_c s) eqn:He2.
                             ---- cbn in Hginc.
                                  pose proof (Hb k i2 inc2 Hvk)
                                    as Hle2.
                                  exfalso. lia.
                             ---- destruct (Hwk Hginc)
                                    as (o2 & vs2 & Ho2 & Hok2 & Hlk2).
                                  exists o2, vs2. cbn. auto.
                         *** cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                             intros Hnone. unfold cstamp in Hnone.
                             match type of Hnone with
                             | (if ?b then _ else _) = _ =>
                                 destruct b eqn:Hik;
                                 try rewrite Hik in Hnone
                             end; [cbn in Hnone; discriminate |].
                             assert (Hik' : inkey k
                                        (map fst (if o_ok o' then o_buf o'
                                                  else []))
                                      = false) by exact Hik.
                             clear Hik. rename Hik' into Hik.
                             rewrite Hm1st.
                             rewrite commit_untouched
                               by (intro Hx; apply inkey_in in Hx;
                                   pose proof (eq_trans (eq_sym Hx) Hik)
                                     as E;
                                   discriminate).
                             try rewrite EOM in Hwk. cbn [fst] in Hwk.
                             exact (Hwk Hnone).
                     +++ intros k i2 inc2 Hvk.
                         pose proof (Hb k i2 inc2 Hvk) as Hle2.
                         cbn [os_inc]. destruct (i2 =? os_c s) eqn:He2; cbn; lia.
              ** intros k i2 inc2 Hsk. cbn [os_stamp] in Hsk. unfold cstamp in Hsk.
           cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
                 match type of Hsk with
                 | (if ?b then _ else _) = _ =>
                     destruct b eqn:Hik; try rewrite Hik in Hsk
                 end;
                 [| assert (Hik' : inkey k
                               (map fst (if o_ok o' then o_buf o' else []))
                             = false) by exact Hik;
                    clear Hik; rename Hik' into Hik].
                 --- cbn in Hsk. injection Hsk as <- <-.
                     destruct (o_ok o') eqn:Hok;
                       [| try rewrite Hok in Hik; cbn in Hik; discriminate].
                     try rewrite Hok in Hik. cbn in Hik.
                     apply inkey_in in Hik.
                     destruct (in_fst_wlookup (o_buf o') k Hik) as [v0 Hv0].
                     split; [lia |].
                     rewrite Nat.eqb_refl.
                     split; [reflexivity |].
                     exists o', (os_stamp s).
                     try rewrite Nat.eqb_refl.
                     split; [reflexivity |]. split; [exact Hok |].
                     try rewrite Hok in Hm1st. cbv beta iota in Hm1st. rewrite Hm1st.
                     rewrite (commit_wlookup (o_buf o') st k v0 Hv0).
                     exact Hv0.
                 --- destruct (Hstamp k i2 inc2 Hsk)
                       as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
                     assert (Hne : i2 <> os_c s) by lia.
                     apply Nat.eqb_neq in Hne.
                     split; [lia |].
                     rewrite Hne.
                     split; [exact Hinc2 |].
                     exists o2, vs2. try rewrite Hne.
                     split; [exact Ho2 |]. split; [exact Hok2 |].
                     rewrite Hm1st.
                     rewrite commit_untouched
                       by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                     try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
                     exact Hlk2.
        -- (* rejected *)
           cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
           assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                           = ((st, bk, nm), rejrcpt)).
           { unfold step. rewrite Hg. reflexivity. }
           split; [exact Hlt |].
           split.
           { try rewrite EOM in Hma |- *.
             apply Hma. rewrite Hstq. rewrite Hstep. reflexivity. }
           split.
           { apply Hrs'. rewrite Hstq. rewrite Hstep. reflexivity. }
           split.
           { intros j0 o0 vs0 Ho0.
             destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
             split; [exact Hprov |]. split; [| exact Hb].
             intros k v Hin.
             pose proof (Hw k v Hin) as Hwk.
             destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
             - cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
             - cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
               try rewrite EOM in Hwk. cbn [fst] in Hwk. exact Hwk. }
           { intros k i2 inc2 Hsk.
             cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
             destruct (Hstamp k i2 inc2 Hsk)
               as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
             split; [lia |]. split; [exact Hinc2 |].
             exists o2, vs2. split; [exact Ho2 |]. split; [exact Hok2 |].
             try rewrite EOM in Hlk2. cbn [fst] in Hlk2. exact Hlk2. }
    + (* no outcome at the head *)
      destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hg.
      * destruct (cstep (st, bk, nm) (fee, non, t, g, p) None)
          as [[m1 r] fl] eqn:EC.
        unfold cstep in EC. rewrite Hg in EC.
        injection EC as EC1 EC2.
        cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
        set (o' := runt (fee, non, t, g, p) (of_state st) (of_bank bk)
                        (of_nonces nm)) in *.
        assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                        = finish st bk nm fee g p o').
        { unfold step. rewrite Hg. reflexivity. }
        assert (Hm1 : m1 = mach_at m0 ts (S (os_c s))).
        { apply Hma. rewrite Hstq.
          exact (f_equal fst (eq_sym EC1)). }
        assert (Hr1 : os_rs s ++ [r]
                      = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
        { apply Hrs'. rewrite Hstq.
          exact (f_equal snd (eq_sym EC1)). }
        assert (Hm1st : fst (fst m1)
                        = commit st (if o_ok o' then o_buf o' else [])).
        { assert (EC1' : finish st bk nm fee g p o' = (m1, r))
            by (rewrite <- Hstep; exact EC1).
          unfold finish in EC1'. cbv zeta in EC1'.
          destruct (o_ok o') eqn:Hok; try rewrite Hok in EC1';
            cbv beta iota in EC1';
            injection EC1' as E1 E2; rewrite <- E1; reflexivity. }
        split; [exact Hlt |]. split; [exact Hm1 |]. split; [exact Hr1 |].
        split.
        -- intros j0 o0 vs0 Ho0. cbn [os_out] in Ho0.
           destruct (j0 =? os_c s) eqn:Hjj.
           ++ apply Nat.eqb_eq in Hjj. subst j0.
              injection Ho0 as <- <-.
              split; [| split].
              ** exists (of_state st), (of_bank bk), (of_nonces nm),
                       (fee, non, t, g, p).
                 split; [exact Hi | reflexivity].
              ** intros k v Hin.
                 assert (Hv : st k = v).
                 { refine (valid_true_In _ st _ k v Hin).
                   unfold o', runt. cbv beta iota zeta.
                   apply valid_self_s. }
                 subst v.
                 destruct (os_stamp s k) as [[i2 inc2] |] eqn:Hsk.
                 --- cbn [stampw os_c os_m os_rs os_inc os_out
                          os_stamp os_rx].
                     intros Hginc.
                     destruct (Hstamp k i2 inc2 Hsk)
                       as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
                     assert (Hne : i2 <> os_c s) by lia.
                     apply Nat.eqb_neq in Hne.
                     exists o2, vs2. try rewrite Hne.
                     split; [exact Ho2 |]. split; [exact Hok2 |].
                     try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
                     exact Hlk2.
                 --- cbn [stampw os_c os_m os_rs os_inc os_out
                          os_stamp os_rx].
                     intros Hnone. unfold cstamp in Hnone.
                     match type of Hnone with
                     | (if ?b then _ else _) = _ =>
                         destruct b eqn:Hik;
                         try rewrite Hik in Hnone
                     end; [cbn in Hnone; discriminate |].
                     assert (Hik' : inkey k
                                (map fst (if o_ok o' then o_buf o'
                                          else []))
                              = false) by exact Hik.
                     clear Hik. rename Hik' into Hik.
                     rewrite Hm1st.
                     rewrite commit_untouched
                       by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                     reflexivity.
              ** intros k i2 inc2 Hsk.
                 destruct (Hstamp k i2 inc2 Hsk) as (Hl2 & Hinc2 & _).
                 assert (Hne : i2 <> os_c s) by lia.
                 apply Nat.eqb_neq in Hne. cbn [os_inc os_c]. rewrite Hne. lia.
           ++ destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
              split; [exact Hprov |]. split.
              ** intros k v Hin.
                 pose proof (Hw k v Hin) as Hwk.
                 destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
                 --- cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                     intros Hginc.
                     destruct (i2 =? os_c s) eqn:He2.
                     +++ cbn in Hginc.
                         pose proof (Hb k i2 inc2 Hvk) as Hle2.
                         exfalso. lia.
                     +++ destruct (Hwk Hginc)
                           as (o2 & vs2 & Ho2 & Hok2 & Hlk2).
                         exists o2, vs2. cbn. auto.
                 --- cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
                     intros Hnone. unfold cstamp in Hnone.
                     match type of Hnone with
                     | (if ?b then _ else _) = _ =>
                         destruct b eqn:Hik;
                         try rewrite Hik in Hnone
                     end; [cbn in Hnone; discriminate |].
                     assert (Hik' : inkey k
                                (map fst (if o_ok o' then o_buf o'
                                          else []))
                              = false) by exact Hik.
                     clear Hik. rename Hik' into Hik.
                     rewrite Hm1st.
                     rewrite commit_untouched
                       by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
                     try rewrite EOM in Hwk. cbn [fst] in Hwk.
                     exact (Hwk Hnone).
              ** intros k i2 inc2 Hvk.
                 pose proof (Hb k i2 inc2 Hvk) as Hle2.
                 cbn [os_inc]. destruct (i2 =? os_c s) eqn:He2; cbn; lia.
        -- intros k i2 inc2 Hsk. cbn [os_stamp] in Hsk. unfold cstamp in Hsk.
           cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
           match type of Hsk with
           | (if ?b then _ else _) = _ =>
               destruct b eqn:Hik; try rewrite Hik in Hsk
           end;
           [| assert (Hik' : inkey k
                         (map fst (if o_ok o' then o_buf o' else []))
                       = false) by exact Hik;
              clear Hik; rename Hik' into Hik].
           ++ cbn in Hsk. injection Hsk as <- <-.
              destruct (o_ok o') eqn:Hok; [| try rewrite Hok in Hik; cbn in Hik; discriminate].
              try rewrite Hok in Hik. cbn in Hik.
              apply inkey_in in Hik.
              destruct (in_fst_wlookup (o_buf o') k Hik) as [v0 Hv0].
              split; [lia |].
              rewrite Nat.eqb_refl.
              split; [reflexivity |].
              exists o', (os_stamp s).
              try rewrite Nat.eqb_refl.
              split; [reflexivity |]. split; [exact Hok |].
              try rewrite Hok in Hm1st. cbv beta iota in Hm1st. rewrite Hm1st.
              rewrite (commit_wlookup (o_buf o') st k v0 Hv0).
              exact Hv0.
           ++ destruct (Hstamp k i2 inc2 Hsk)
                as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
              assert (Hne : i2 <> os_c s) by lia.
              apply Nat.eqb_neq in Hne.
              split; [lia |].
              rewrite Hne.
              split; [exact Hinc2 |].
              exists o2, vs2. try rewrite Hne.
              split; [exact Ho2 |]. split; [exact Hok2 |].
              rewrite Hm1st.
              rewrite commit_untouched
                by (intro Hx; apply inkey_in in Hx;
                       pose proof (eq_trans (eq_sym Hx) Hik) as E;
                       discriminate).
              try rewrite EOM in Hlk2. cbn [fst] in Hlk2.
              exact Hlk2.
      * (* rejected, no outcome *)
        cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
        assert (Hstep : step (st, bk, nm) (fee, non, t, g, p)
                        = ((st, bk, nm), rejrcpt)).
        { unfold step. rewrite Hg. reflexivity. }
        split; [exact Hlt |].
        split.
        { try rewrite EOM in Hma |- *.
          apply Hma. rewrite Hstq. rewrite Hstep. reflexivity. }
        split.
        { apply Hrs'. rewrite Hstq. rewrite Hstep. reflexivity. }
        split.
        { intros j0 o0 vs0 Ho0.
          destruct (Hout j0 o0 vs0 Ho0) as (Hprov & Hw & Hb).
          split; [exact Hprov |]. split; [| exact Hb].
          intros k v Hin.
          pose proof (Hw k v Hin) as Hwk.
          destruct (vs0 k) as [[i2 inc2] |] eqn:Hvk.
          - cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *. exact Hwk.
          - cbn [stampw os_c os_m os_rs os_inc os_out os_stamp os_rx] in Hwk |- *.
            try rewrite EOM in Hwk. cbn [fst] in Hwk. exact Hwk. }
        { intros k i2 inc2 Hsk.
          cbn [os_c os_m os_rs os_inc os_out os_stamp os_rx].
          destruct (Hstamp k i2 inc2 Hsk)
            as (Hl2 & Hinc2 & o2 & vs2 & Ho2 & Hok2 & Hlk2).
          split; [lia |]. split; [exact Hinc2 |].
          exists o2, vs2. split; [exact Ho2 |]. split; [exact Hok2 |].
          try rewrite EOM in Hlk2. cbn [fst] in Hlk2. exact Hlk2. }
Qed.

Lemma reach_inv :
  forall ts m0 acts s,
    oinv m0 ts s -> oinv m0 ts (fold_left (ostep ts) acts s).
Proof.
  intros ts m0 acts. induction acts as [| a acts' IH]; intros s Hs; cbn.
  - exact Hs.
  - apply IH. apply ostep_inv. exact Hs.
Qed.

Lemma oinit_inv : forall ts m0, oinv m0 ts (oinit m0).
Proof.
  intros ts m0.
  split; [cbn; lia |]. split; [reflexivity |]. split; [reflexivity |].
  split.
  - intros j o vs H. discriminate.
  - intros k i2 inc2 H. discriminate.
Qed.

(** Safety: however executions, validations, and commits interleave, once
    the wavefront has crossed the block the committed machine and receipts
    are sequential execution's. *)

Theorem op_safety :
  forall ts m0 acts,
    os_c (reach ts (oinit m0) acts) = length ts ->
    os_m (reach ts (oinit m0) acts) = fst (seq_execr m0 ts)
    /\ os_rs (reach ts (oinit m0) acts) = snd (seq_execr m0 ts).
Proof.
  intros ts m0 acts Hdone.
  pose proof (reach_inv ts m0 acts (oinit m0) (oinit_inv ts m0)) as Hs.
  destruct Hs as [Hc [Hm [Hr _]]].
  unfold reach in *.
  rewrite Hdone in Hm, Hr.
  split.
  - rewrite Hm. apply mach_at_full.
  - rewrite Hr. apply firstn_all2. rewrite seq_rcpt_len. lia.
Qed.

(** Liveness: a commit action always advances the wavefront, executions
    and eager validations never retard it, so any schedule containing at
    least as many commit actions as the block is long finishes the block,
    whatever else it interleaves and in whatever order. *)

Lemma commit_advances :
  forall ts s,
    os_c s < length ts ->
    os_c (ostep ts s ACommit) = S (os_c s).
Proof.
  intros ts s Hlt. cbn [ostep].
  destruct (os_c s <? length ts) eqn:Hb;
    [| apply Nat.ltb_ge in Hb; lia].
  destruct (nth_error ts (os_c s)) as [i |] eqn:Hi;
    [| exfalso; apply nth_error_None in Hi; lia].
  destruct (os_m s) as [[st bk] nm].
  destruct i as [[[[fee non] t] g] p].
  destruct (os_out s (os_c s)) as [[o vs] |].
  - destruct (vercheck (o_slog o) vs (os_stamp s)
              && bvalid bk (o_blog o) && nvalid nm (o_nlog o)
              && gateb bk nm (fee, non, t, g, p)).
    + destruct (finish st bk nm fee g p o) as [m1 r]. reflexivity.
    + destruct (gateb bk nm (fee, non, t, g, p)).
      * destruct (cstep (st, bk, nm) (fee, non, t, g, p) (Some o))
          as [[m1 r] fl].
        destruct fl; reflexivity.
      * reflexivity.
  - destruct (gateb bk nm (fee, non, t, g, p)).
    + destruct (cstep (st, bk, nm) (fee, non, t, g, p) None)
        as [[m1 r] fl].
      reflexivity.
    + reflexivity.
Qed.

Lemma exec_keeps :
  forall ts s j, os_c (ostep ts s (AExec j)) = os_c s.
Proof.
  intros ts s j. cbn [ostep].
  destruct ((os_c s <=? j) && (j <? length ts)); [| reflexivity].
  destruct (nth_error ts j) as [i |]; reflexivity.
Qed.

Lemma aval_keeps :
  forall ts s j, os_c (ostep ts s (AVal j)) = os_c s.
Proof.
  intros ts s j. cbn [ostep].
  destruct ((os_c s <=? j) && (j <? length ts)); [| reflexivity].
  destruct (os_out s j) as [[o vs] |]; [| reflexivity].
  destruct (vercheck (o_slog o) vs (ostamp s j)); reflexivity.
Qed.

Definition is_commit (a : oact) : bool :=
  match a with ACommit => true | _ => false end.

Lemma osc_lower :
  forall ts acts s,
    Nat.min (length ts) (os_c s + length (filter is_commit acts))
    <= os_c (fold_left (ostep ts) acts s).
Proof.
  intros ts acts. induction acts as [| a acts' IH]; intros s; cbn [fold_left].
  - cbn [filter length]. lia.
  - destruct a as [j | j |].
    + cbn [filter is_commit].
      etransitivity; [| apply IH].
      rewrite exec_keeps. lia.
    + cbn [filter is_commit].
      etransitivity; [| apply IH].
      rewrite aval_keeps. lia.
    + cbn [filter is_commit length].
      etransitivity; [| apply IH].
      destruct (Nat.lt_ge_cases (os_c s) (length ts)) as [Hlt | Hge].
      * rewrite commit_advances by exact Hlt. lia.
      * assert (Hstay : os_c (ostep ts s ACommit) = os_c s).
        { cbn [ostep]. destruct (os_c s <? length ts) eqn:Hb.
          - apply Nat.ltb_lt in Hb. lia.
          - reflexivity. }
        rewrite Hstay. lia.
Qed.

Theorem op_liveness :
  forall ts m0 acts,
    length ts <= length (filter is_commit acts) ->
    os_c (reach ts (oinit m0) acts) = length ts.
Proof.
  intros ts m0 acts Hn.
  pose proof (osc_lower ts acts (oinit m0)) as Hlow.
  pose proof (reach_inv ts m0 acts (oinit m0) (oinit_inv ts m0)) as [Hc _].
  unfold reach in *. cbn [os_c oinit] in *.
  lia.
Qed.

(** The commit-time re-execution count never exceeds the wavefront: each
    position re-executes at most once, at its own commit. *)

Lemma orx_step :
  forall ts s a,
    os_rx (ostep ts s a) + os_c s <= os_rx s + os_c (ostep ts s a).
Proof.
  intros ts s a. destruct a as [j | j |]; cbn [ostep].
  - destruct ((os_c s <=? j) && (j <? length ts)); [| lia].
    destruct (nth_error ts j) as [i |]; cbn; lia.
  - destruct ((os_c s <=? j) && (j <? length ts)); [| lia].
    destruct (os_out s j) as [[o vs] |]; [| lia].
    destruct (vercheck (o_slog o) vs (ostamp s j)); cbn; lia.
  - destruct (os_c s <? length ts); [| lia].
    destruct (nth_error ts (os_c s)) as [i |]; [| lia].
    destruct (os_m s) as [[st bk] nm].
    destruct i as [[[[fee non] t] g] p].
    destruct (os_out s (os_c s)) as [[o vs] |].
    + destruct (vercheck (o_slog o) vs (os_stamp s)
                && bvalid bk (o_blog o) && nvalid nm (o_nlog o)
                && gateb bk nm (fee, non, t, g, p)).
      * destruct (finish st bk nm fee g p o) as [m1 r]. cbn. lia.
      * destruct (gateb bk nm (fee, non, t, g, p)).
        -- destruct (cstep (st, bk, nm) (fee, non, t, g, p) (Some o))
             as [[m1 r] fl].
           destruct fl; cbn; lia.
        -- cbn. lia.
    + destruct (gateb bk nm (fee, non, t, g, p)).
      * destruct (cstep (st, bk, nm) (fee, non, t, g, p) None)
          as [[m1 r] fl].
        cbn. lia.
      * cbn. lia.
Qed.

Theorem op_reexec_bound :
  forall ts m0 acts,
    os_rx (reach ts (oinit m0) acts) <= os_c (reach ts (oinit m0) acts).
Proof.
  intros ts m0 acts. unfold reach.
  assert (H : forall s, os_rx (fold_left (ostep ts) acts s) + os_c s
                        <= os_rx s + os_c (fold_left (ostep ts) acts s)).
  { induction acts as [| a acts' IH]; intros s; cbn [fold_left]; [lia |].
    pose proof (orx_step ts s a).
    pose proof (IH (ostep ts s a)). lia. }
  pose proof (H (oinit m0)). cbn [os_rx os_c oinit] in *. lia.
Qed.

(** Fairness: if every window of [K] consecutive actions contains a
    commit, the block finishes within [length ts * K] actions. *)

Lemma firstn_plus :
  forall (A : Type) n m (l : list A),
    firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros A n. induction n as [| n' IH]; intros m l;
    cbn [firstn skipn Nat.add app].
  - reflexivity.
  - destruct l as [| x l'].
    + rewrite ?skipn_nil, ?firstn_nil. reflexivity.
    + cbn [firstn skipn app]. f_equal. apply IH.
Qed.

Lemma existsb_filter_le :
  forall (A : Type) (f : A -> bool) l,
    existsb f l = true -> 1 <= length (filter f l).
Proof.
  intros A f l. induction l as [| y r IH]; intros H; [discriminate |].
  cbn [existsb] in H. apply orb_true_iff in H.
  cbn [filter].
  destruct H as [H | H].
  - rewrite H. cbn. lia.
  - destruct (f y); cbn; [lia | exact (IH H)].
Qed.

Lemma kdense_commits :
  forall (K : nat) (acts : list oact),
    1 <= K ->
    (forall pre win post,
        acts = pre ++ win ++ post -> length win = K ->
        existsb is_commit win = true) ->
    forall q, q * K <= length acts ->
    q <= length (filter is_commit (firstn (q * K) acts)).
Proof.
  intros K acts HK Hd.
  induction q as [| q' IH]; intros Hq; [lia |].
  replace (S q' * K) with (q' * K + K) in Hq |- * by lia.
  rewrite firstn_plus.
  rewrite filter_app, length_app.
  assert (Hwin : existsb is_commit (firstn K (skipn (q' * K) acts)) = true).
  { apply (Hd (firstn (q' * K) acts)
             (firstn K (skipn (q' * K) acts))
             (skipn K (skipn (q' * K) acts))).
    - rewrite (firstn_skipn K (skipn (q' * K) acts)).
      rewrite (firstn_skipn (q' * K) acts).
      reflexivity.
    - apply firstn_length_le.
      rewrite length_skipn. lia. }
  pose proof (existsb_filter_le _ is_commit _ Hwin).
  pose proof (IH ltac:(lia)).
  lia.
Qed.

Theorem op_fair_completion :
  forall ts m0 acts K,
    1 <= K ->
    (forall pre win post,
        acts = pre ++ win ++ post -> length win = K ->
        existsb is_commit win = true) ->
    length ts * K <= length acts ->
    os_c (reach ts (oinit m0) (firstn (length ts * K) acts)) = length ts.
Proof.
  intros ts m0 acts K HK Hd Hlen.
  apply op_liveness.
  pose proof (kdense_commits K acts HK Hd (length ts) Hlen). lia.
Qed.

(** ** The operational fast path

    [trueout] is the outcome position [i] produces against its true prefix
    machine.  When executed lower positions hold true outcomes, the
    operational overlays reconstruct the true prefix exactly: storage
    through the committed buffers, bank and nonces through the recorded
    effects.  Executing every position in index order and then committing
    the block therefore validates everywhere: the committed machine and
    receipts are sequential execution's and not one position re-executes.
    Admission of every position along the true sequence is assumed, since
    an executed-but-rejected position's buffer is not part of the
    sequential state. *)

Definition trueout (m0 : mach) (ts : list item) (i : nat) : out :=
  runt (nth i ts ditem)
       (of_state (fst (fst (mach_at m0 ts i))))
       (of_bank (snd (fst (mach_at m0 ts i))))
       (of_nonces (snd (mach_at m0 ts i))).

Lemma beff_step :
  forall m0 ts j,
    j < length ts ->
    beff (nth j ts ditem) (trueout m0 ts j)
         (snd (fst (mach_at m0 ts j)), snd (mach_at m0 ts j))
    = (snd (fst (mach_at m0 ts (S j))), snd (mach_at m0 ts (S j))).
Proof.
  intros m0 ts j Hj.
  rewrite (mach_at_S ts m0 j Hj).
  unfold trueout.
  destruct (mach_at m0 ts j) as [[stq bkq] nmq].
  destruct (nth j ts ditem) as [[[[fee non] t] g] p].
  cbn [fst snd].
  unfold beff, step.
  destruct (gateb bkq nmq (fee, non, t, g, p)) eqn:Hg.
  - unfold finish. cbv zeta.
    destruct (o_ok (runt (fee, non, t, g, p) (of_state stq) (of_bank bkq)
                         (of_nonces nmq))) eqn:Hok; cbv beta iota;
      cbn [fst snd]; reflexivity.
  - cbn [fst snd]. reflexivity.
Qed.

Lemma obuf_trueout :
  forall m0 ts s i cap,
    i < length ts ->
    os_out s i = Some (trueout m0 ts i, cap) ->
    gateb (snd (fst (mach_at m0 ts i))) (snd (mach_at m0 ts i))
          (nth i ts ditem) = true ->
    obuf s i = cbuf m0 ts i.
Proof.
  intros m0 ts s i cap Hi Ho Hg.
  unfold obuf, cbuf. rewrite Ho.
  unfold trueout.
  destruct (mach_at m0 ts i) as [[stq bkq] nmq].
  destruct (nth i ts ditem) as [[[[fee non] t] g] p].
  cbn [fst snd] in Hg.
  unfold step. rewrite Hg.
  unfold finish. cbv zeta.
  destruct (o_ok (runt (fee, non, t, g, p) (of_state stq) (of_bank bkq)
                       (of_nonces nmq))) eqn:Hok; cbv beta iota;
    cbn [fst snd];
    match goal with
    | |- (if ?b then _ else _) = _ =>
        first [ replace b with true by (symmetry; exact Hok)
              | replace b with false by (symmetry; exact Hok) ]
    end; reflexivity.
Qed.

Lemma ostor_go_true :
  forall ts m0 s cnt from,
    from + cnt <= length ts ->
    (forall i, from <= i -> i < from + cnt -> obuf s i = cbuf m0 ts i) ->
    forall k,
      ostor_go (fst (fst (mach_at m0 ts from))) (obuf s) from cnt k
      = fst (fst (mach_at m0 ts (from + cnt))) k.
Proof.
  intros ts m0 s cnt. induction cnt as [| c IH]; intros from Hle Hbuf k.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [ostor_go].
    rewrite (Hbuf from ltac:(lia) ltac:(lia)).
    rewrite <- (stor_mach_at_S ts m0 from ltac:(lia)).
    replace (from + S c) with (S from + c) by lia.
    apply IH; [lia |].
    intros i Hi1 Hi2. apply Hbuf; lia.
Qed.

Lemma obknm_go_true :
  forall ts m0 s cnt from,
    from + cnt <= length ts ->
    (forall i, from <= i -> i < from + cnt -> exists cap,
        os_out s i = Some (trueout m0 ts i, cap)) ->
    obknm_go ts s (snd (fst (mach_at m0 ts from)), snd (mach_at m0 ts from))
             from cnt
    = (snd (fst (mach_at m0 ts (from + cnt))),
       snd (mach_at m0 ts (from + cnt))).
Proof.
  intros ts m0 s cnt. induction cnt as [| c IH]; intros from Hle Hout.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [obknm_go].
    destruct (Hout from ltac:(lia) ltac:(lia)) as [cap Hof].
    rewrite Hof.
    rewrite (beff_step m0 ts from ltac:(lia)).
    replace (from + S c) with (S from + c) by lia.
    apply IH; [lia |].
    intros i Hi1 Hi2. apply Hout; lia.
Qed.

Theorem op_overlay_true :
  forall ts m0 s j,
    os_c s = 0 -> os_m s = m0 -> j <= length ts ->
    (forall i, i < j -> obuf s i = cbuf m0 ts i) ->
    forall k, ostor s j k = fst (fst (mach_at m0 ts j)) k.
Proof.
  intros ts m0 s j Hc Hm Hj Hbuf k.
  unfold ostor. rewrite Hc, Hm, Nat.sub_0_r.
  exact (ostor_go_true ts m0 s j 0 ltac:(lia)
           (ltac:(intros i Hi1 Hi2; apply Hbuf; lia)) k).
Qed.

Lemma exec_phase :
  forall ts m0,
    (forall i, i < length ts ->
        gateb (snd (fst (mach_at m0 ts i))) (snd (mach_at m0 ts i))
              (nth i ts ditem) = true) ->
    forall j, j <= length ts ->
    os_c (reach ts (oinit m0) (map AExec (seq 0 j))) = 0
    /\ os_m (reach ts (oinit m0) (map AExec (seq 0 j))) = m0
    /\ os_rs (reach ts (oinit m0) (map AExec (seq 0 j))) = []
    /\ os_rx (reach ts (oinit m0) (map AExec (seq 0 j))) = 0
    /\ (forall i, j <= i ->
          os_out (reach ts (oinit m0) (map AExec (seq 0 j))) i = None)
    /\ (forall i, i < j -> exists cap,
          os_out (reach ts (oinit m0) (map AExec (seq 0 j))) i
          = Some (trueout m0 ts i, cap)).
Proof.
  intros ts m0 Hgate j.
  induction j as [| j IH]; intros Hj.
  - refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
              (conj _ _))))).
    + intros i _. reflexivity.
    + intros i Hi. lia.
  - rewrite seq_S, map_app, reach_app.
    destruct (IH ltac:(lia)) as (Hc & Hm & Hr & Hx & Hnone & Htrue).
    set (sj := reach ts (oinit m0) (map AExec (seq 0 j))) in *.
    assert (Hbuf : forall i, i < j -> obuf sj i = cbuf m0 ts i).
    { intros i Hi.
      destruct (Htrue i Hi) as [cap Hoi].
      exact (obuf_trueout m0 ts sj i cap ltac:(lia) Hoi
               (Hgate i ltac:(lia))). }
    assert (Hov : forall k, ostor sj j k = fst (fst (mach_at m0 ts j)) k).
    { apply op_overlay_true; try assumption. lia. }
    assert (Hbk : obknm ts sj j
                  = (snd (fst (mach_at m0 ts j)), snd (mach_at m0 ts j))).
    { unfold obknm. rewrite Hc, Hm, Nat.sub_0_r.
      exact (obknm_go_true ts m0 sj j 0 ltac:(lia)
               (ltac:(intros i Hi1 Hi2; apply Htrue; lia))). }
    assert (Hrun : runt (nth j ts ditem)
                     (of_state (ostor sj j))
                     (of_bank (fst (obknm ts sj j)))
                     (of_nonces (snd (obknm ts sj j)))
                   = trueout m0 ts j).
    { unfold trueout. symmetry.
      destruct (nth j ts ditem) as [[[[fee non] t] g] p].
      unfold runt. cbv beta iota zeta.
      apply replay.
      - intros k v Hin.
        assert (Hv : ostor sj j k = v).
        { refine (valid_true_In _ (ostor sj j) _ k v Hin).
          apply valid_self_s. }
        rewrite <- Hv. exact (eq_sym (Hov k)).
      - intros a v Hin.
        assert (Hv : fst (obknm ts sj j) a = v).
        { refine (bvalid_true_In _ (fst (obknm ts sj j)) _ a v Hin).
          apply bvalid_self_b. }
        rewrite <- Hv. rewrite Hbk. reflexivity.
      - intros a v Hin.
        assert (Hv : snd (obknm ts sj j) a = v).
        { refine (bvalid_true_In _ (snd (obknm ts sj j)) _ a v Hin).
          pose proof (nvalid_self_n g (g - c_base C) fee t
                        (of_state (ostor sj j))
                        (of_bank (fst (obknm ts sj j)))
                        (snd (obknm ts sj j)) 0 0 0 [] zerof
                        (deb0 fee (g * (BF + p))) [] (aacc0 fee)) as Hn.
          unfold nvalid in Hn. exact Hn. }
        rewrite <- Hv. rewrite Hbk. reflexivity. }
    cbn [map reach fold_left Nat.add].
    cbn [ostep].
    assert (Hguard : (os_c sj <=? j) && (j <? length ts) = true).
    { rewrite Hc. cbn. apply Nat.ltb_lt. lia. }
    rewrite Hguard.
    assert (Hn : nth_error ts j = Some (nth j ts ditem))
      by (apply nth_error_nth'; lia).
    rewrite Hn.
    cbn [os_c os_m os_rs os_rx os_out].
    refine (conj Hc (conj Hm (conj Hr (conj Hx (conj _ _))))).
    + intros i Hi. cbn beta.
      destruct (i =? j) eqn:He.
      * apply Nat.eqb_eq in He. lia.
      * apply Hnone. lia.
    + intros i Hi. cbn beta.
      destruct (i =? j) eqn:He.
      * apply Nat.eqb_eq in He. subst i.
        exists (ostamp sj j).
        rewrite Hrun. reflexivity.
      * apply Htrue. apply Nat.eqb_neq in He. lia.
Qed.

Lemma commit_phase :
  forall ts m0 cnt s,
    oinv m0 ts s ->
    os_c s + cnt = length ts ->
    (forall i, os_c s <= i -> i < length ts -> exists cap,
        os_out s i = Some (trueout m0 ts i, cap)) ->
    os_c (reach ts s (repeat ACommit cnt)) = length ts
    /\ os_rx (reach ts s (repeat ACommit cnt)) = os_rx s.
Proof.
  intros ts m0 cnt. induction cnt as [| c IH]; intros s Hinv Hlen Hout.
  - cbn. split; [lia | reflexivity].
  - cbn [repeat reach fold_left].
    pose proof Hinv as [Hc [Hm [Hr [Houti Hstamp]]]].
    assert (Hstep1 : os_c (ostep ts s ACommit) = S (os_c s)
                     /\ os_rx (ostep ts s ACommit) = os_rx s
                     /\ (forall i, os_out (ostep ts s ACommit) i
                                   = os_out s i)).
    { cbn [ostep].
      assert (Hb : (os_c s <? length ts) = true)
        by (apply Nat.ltb_lt; lia).
      rewrite Hb.
      assert (Hn : nth_error ts (os_c s) = Some (nth (os_c s) ts ditem))
        by (apply nth_error_nth'; lia).
      rewrite Hn.
      destruct (os_m s) as [[st bk] nm] eqn:EOM.
      assert (HmS : mach_at m0 ts (os_c s) = (st, bk, nm))
        by (symmetry; exact Hm).
      destruct (nth (os_c s) ts ditem) as [[[[fee non] t] g] p] eqn:EN.
      destruct (Hout (os_c s) ltac:(lia) ltac:(lia)) as [cap Hoc].
      rewrite Hoc.
      destruct (vercheck (o_slog (trueout m0 ts (os_c s))) cap (os_stamp s)
                && bvalid bk (o_blog (trueout m0 ts (os_c s)))
                && nvalid nm (o_nlog (trueout m0 ts (os_c s)))
                && gateb bk nm (fee, non, t, g, p)) eqn:HA.
      - destruct (finish st bk nm fee g p (trueout m0 ts (os_c s)))
          as [m1 r].
        cbn. split; [reflexivity |]. split; [reflexivity |].
        intros i. reflexivity.
      - destruct (gateb bk nm (fee, non, t, g, p)) eqn:Hg.
        + assert (Hvchk : vcheck st bk nm (trueout m0 ts (os_c s)) = true).
          { unfold trueout. rewrite EN, HmS. cbn [fst snd].
            unfold vcheck, runt. cbv beta iota zeta.
            rewrite valid_self_s, bvalid_self_b, nvalid_self_n.
            reflexivity. }
          destruct (cstep (st, bk, nm) (fee, non, t, g, p)
                      (Some (trueout m0 ts (os_c s)))) as [[m1 r] fl]
            eqn:EC.
          unfold cstep in EC. rewrite Hg, Hvchk in EC.
          injection EC as EC1 EC2.
          rewrite <- EC2.
          cbn. split; [reflexivity |]. split; [reflexivity |].
          intros i. reflexivity.
        + cbn. split; [reflexivity |]. split; [reflexivity |].
          intros i. reflexivity. }
    destruct Hstep1 as (H1c & H1x & H1o).
    assert (Hout1 : forall i, os_c (ostep ts s ACommit) <= i ->
               i < length ts -> exists cap,
               os_out (ostep ts s ACommit) i = Some (trueout m0 ts i, cap)).
    { intros i Hi1 Hi2. rewrite H1o. apply Hout; [| exact Hi2].
      rewrite H1c in Hi1. lia. }
    destruct (IH (ostep ts s ACommit) (ostep_inv ts m0 s ACommit Hinv)
                ltac:(rewrite H1c; lia) Hout1) as [IHc IHx].
    split; [exact IHc |].
    rewrite <- H1x. exact IHx.
Qed.

Theorem op_fast_path :
  forall ts m0,
    (forall i, i < length ts ->
        gateb (snd (fst (mach_at m0 ts i))) (snd (mach_at m0 ts i))
              (nth i ts ditem) = true) ->
    os_c (reach ts (oinit m0)
            (map AExec (seq 0 (length ts)) ++ repeat ACommit (length ts)))
    = length ts
    /\ os_m (reach ts (oinit m0)
              (map AExec (seq 0 (length ts))
               ++ repeat ACommit (length ts)))
      = fst (seq_execr m0 ts)
    /\ os_rs (reach ts (oinit m0)
               (map AExec (seq 0 (length ts))
                ++ repeat ACommit (length ts)))
      = snd (seq_execr m0 ts)
    /\ os_rx (reach ts (oinit m0)
               (map AExec (seq 0 (length ts))
                ++ repeat ACommit (length ts)))
      = 0.
Proof.
  intros ts m0 Hgate.
  destruct (exec_phase ts m0 Hgate (length ts) (le_n _))
    as (Hc & Hm & Hr & Hx & Hnone & Htrue).
  set (se := reach ts (oinit m0) (map AExec (seq 0 (length ts)))) in *.
  assert (Hinv : oinv m0 ts se)
    by (apply reach_inv; apply oinit_inv).
  destruct (commit_phase ts m0 (length ts) se Hinv
              ltac:(rewrite Hc; lia)
              ltac:(intros i Hi1 Hi2; exact (Htrue i Hi2)))
    as [Hfc Hfx].
  assert (Hdone : os_c (reach ts (oinit m0)
                     (map AExec (seq 0 (length ts))
                      ++ repeat ACommit (length ts))) = length ts)
    by (rewrite reach_app; exact Hfc).
  destruct (op_safety ts m0 _ Hdone) as [Hsm Hsr].
  split; [exact Hdone |].
  split; [exact Hsm |].
  split; [exact Hsr |].
  rewrite reach_app. fold se. rewrite Hfx. exact Hx.
Qed.

(* __SENTINEL__ *)

End Machine.
