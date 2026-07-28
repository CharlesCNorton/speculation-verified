(******************************************************************************)
(*                                                                            *)
(*                 Optimistic Parallel Transaction Execution                  *)
(*                                                                            *)
(*     Optimistic concurrency control over a linearly ordered block of        *)
(*     transactions: speculative runs against arbitrary read sources,         *)
(*     ordered commit-time validation by storage, balance, and nonce read     *)
(*     logs, re-execution on conflict.  Contract-scoped storage, calls with   *)
(*     per-frame reverts, an in-flight bank with point-of-pay settlement,     *)
(*     per-operation gas costs with refunds.  Machine-checked safety,         *)
(*     scheduler optimality, retry convergence, conflict freedom, parallel    *)
(*     depth, an operational concurrent scheduler with liveness, and gas,     *)
(*     transfer, nonce, and supply ledgers.                                   *)
(*                                                                            *)
(*     Reference: Kung HT, Robinson JT. On optimistic methods for             *)
(*     concurrency control. ACM TODS. 1981;6(2):213-226.                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: July 27, 2026                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List Arith Bool Lia Permutation NArith.
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

(** ** Transfers

    A transfer carries its sender: calls make contracts pay from their own
    accounts.  Settlement applies transfers in program order; [apply_ok]
    certifies stepwise sufficiency, under which [apply_law] is the exact
    per-account ledger. *)

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

    [TBal] reads an account's in-flight balance: the prefix-bank answer
    adjusted by the transaction's own upfront gas hold, settled payments,
    and receipts.  [TPay] settles at the point of pay against the in-flight
    bank and passes the outcome to its continuation.  [TNonce] reads the
    prefix nonce map.  [TCall] runs another contract's code in its own
    storage scope and frame; a reverted frame keeps its logs and gas but
    surrenders its writes, events, transfers, refunds, and bank deltas. *)

Inductive tx : Type :=
| TDone   : tx
| TRevert : tx
| TWrite  : addr -> val -> tx -> tx
| TRead   : addr -> (val -> tx) -> tx
| TBal    : addr -> (nat -> tx) -> tx
| TNonce  : addr -> (nat -> tx) -> tx
| TWhile  : addr -> tx -> tx -> tx
| TEmit   : val -> tx -> tx
| TPay    : addr -> nat -> (bool -> tx) -> tx
| TCall   : addr -> (bool -> tx) -> tx.

Fixpoint tseq (t1 t2 : tx) : tx :=
  match t1 with
  | TDone => t2
  | TRevert => TRevert
  | TWrite a v k => TWrite a v (tseq k t2)
  | TRead a k => TRead a (fun v => tseq (k v) t2)
  | TBal a k => TBal a (fun v => tseq (k v) t2)
  | TNonce a k => TNonce a (fun v => tseq (k v) t2)
  | TWhile a b k => TWhile a b (tseq k t2)
  | TEmit e k => TEmit e (tseq k t2)
  | TPay d amt k => TPay d amt (fun ok => tseq (k ok) t2)
  | TCall c k => TCall c (fun ok => tseq (k ok) t2)
  end.

Fixpoint trepeat (n : nat) (body : tx) : tx :=
  match n with
  | 0 => TDone
  | S m => tseq body (trepeat m body)
  end.

(** A block item: fee account (transaction sender, top-level executing
    account, and nonce owner), the transaction, its gas limit, and its gas
    price. *)

Definition item : Type := (addr * tx * nat * nat)%type.

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

(** ** Per-operation gas costs *)

Record costs : Type := Costs {
  c_write : nat; c_read : nat; c_bal : nat; c_nonce : nat;
  c_while : nat; c_emit : nat; c_pay : nat; c_call : nat
}.

(** ** Outcomes

    An outcome carries the three read logs, the write overlay, events and
    settled transfers in program order, the completion flag, remaining gas,
    accrued refund, the in-flight bank deltas, and the next read ordinals.
    The record representation lets every projection of a composed outcome
    reduce definitionally, which is what retires the tuple-destruct
    boilerplate the earlier development repeated across its inductions. *)

Record out : Type := Out {
  o_slog : list (key * val);
  o_blog : list (addr * nat);
  o_nlog : list (addr * nat);
  o_buf  : buffer;
  o_evs  : list val;
  o_tvs  : list transfer;
  o_ok   : bool;
  o_gas  : nat;
  o_ref  : nat;
  o_cred : addr -> nat;
  o_deb  : addr -> nat;
  o_n    : nat;
  o_bn   : nat;
  o_nn   : nat
}.

Section Machine.

Variable C : costs.
Variable R : nat.
Variable CODE : addr -> tx.
Variable CB : addr.

(** Out-of-gas (or out-of-fuel) halt: a frame revert charging nothing
    further.  Runs are invoked with fuel equal to gas; with every cost at
    least one the fuel bound is never the binding constraint. *)

Definition oog (gas : nat) (w : buffer) (cred deb : addr -> nat)
               (n bn nn : nat) : out :=
  Out [] [] [] w [] [] false gas 0 cred deb n bn nn.

Fixpoint runp (f gas : nat) (cur : addr) (t : tx)
              (rd : reader) (brd : breader) (nrd : nreader)
              (n bn nn : nat) (w : buffer)
              (cred deb : addr -> nat) : out :=
  match t with
  | TDone => Out [] [] [] w [] [] true gas 0 cred deb n bn nn
  | TRevert => Out [] [] [] w [] [] false gas 0 cred deb n bn nn
  | TWrite a v k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_write C <=? gas
          then
            let o := runp f' (gas - c_write C) cur k rd brd nrd n bn nn
                          (((cur, a), v) :: w) cred deb in
            Out (o_slog o) (o_blog o) (o_nlog o) (o_buf o) (o_evs o) (o_tvs o)
                (o_ok o) (o_gas o) ((if v =? 0 then R else 0) + o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
          else oog gas w cred deb n bn nn
      end
  | TRead a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_read C <=? gas
          then
            match wlookup w (cur, a) with
            | Some v =>
                runp f' (gas - c_read C) cur (k v) rd brd nrd n bn nn w cred deb
            | None =>
                let v := rd n (cur, a) in
                let o := runp f' (gas - c_read C) cur (k v) rd brd nrd
                              (S n) bn nn w cred deb in
                Out (((cur, a), v) :: o_slog o) (o_blog o) (o_nlog o) (o_buf o)
                    (o_evs o) (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
            end
          else oog gas w cred deb n bn nn
      end
  | TBal a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_bal C <=? gas
          then
            let raw := brd bn a in
            let o := runp f' (gas - c_bal C) cur (k (raw + cred a - deb a))
                          rd brd nrd n (S bn) nn w cred deb in
            Out (o_slog o) ((a, raw) :: o_blog o) (o_nlog o) (o_buf o)
                (o_evs o) (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
          else oog gas w cred deb n bn nn
      end
  | TNonce a k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_nonce C <=? gas
          then
            let raw := nrd nn a in
            let o := runp f' (gas - c_nonce C) cur (k raw) rd brd nrd
                          n bn (S nn) w cred deb in
            Out (o_slog o) (o_blog o) ((a, raw) :: o_nlog o) (o_buf o)
                (o_evs o) (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
          else oog gas w cred deb n bn nn
      end
  | TWhile a b k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_while C <=? gas
          then
            match wlookup w (cur, a) with
            | Some v =>
                if v =? 0
                then runp f' (gas - c_while C) cur k rd brd nrd n bn nn w cred deb
                else runp f' (gas - c_while C) cur (tseq b (TWhile a b k))
                          rd brd nrd n bn nn w cred deb
            | None =>
                let v := rd n (cur, a) in
                let o := if v =? 0
                         then runp f' (gas - c_while C) cur k rd brd nrd
                                   (S n) bn nn w cred deb
                         else runp f' (gas - c_while C) cur (tseq b (TWhile a b k))
                                   rd brd nrd (S n) bn nn w cred deb in
                Out (((cur, a), v) :: o_slog o) (o_blog o) (o_nlog o) (o_buf o)
                    (o_evs o) (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                    (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
            end
          else oog gas w cred deb n bn nn
      end
  | TEmit e k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_emit C <=? gas
          then
            let o := runp f' (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb in
            Out (o_slog o) (o_blog o) (o_nlog o) (o_buf o) (e :: o_evs o)
                (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
          else oog gas w cred deb n bn nn
      end
  | TPay d amt k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_pay C <=? gas
          then
            let raw := brd bn cur in
            if amt <=? raw + cred cur - deb cur
            then
              let o := runp f' (gas - c_pay C) cur (k true) rd brd nrd
                            n (S bn) nn w
                            (bupd cred d (cred d + amt))
                            (bupd deb cur (deb cur + amt)) in
              Out (o_slog o) ((cur, raw) :: o_blog o) (o_nlog o) (o_buf o)
                  (o_evs o) ((cur, d, amt) :: o_tvs o) (o_ok o) (o_gas o)
                  (o_ref o) (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
            else
              let o := runp f' (gas - c_pay C) cur (k false) rd brd nrd
                            n (S bn) nn w cred deb in
              Out (o_slog o) ((cur, raw) :: o_blog o) (o_nlog o) (o_buf o)
                  (o_evs o) (o_tvs o) (o_ok o) (o_gas o) (o_ref o)
                  (o_cred o) (o_deb o) (o_n o) (o_bn o) (o_nn o)
          else oog gas w cred deb n bn nn
      end
  | TCall c k =>
      match f with
      | 0 => oog gas w cred deb n bn nn
      | S f' =>
          if c_call C <=? gas
          then
            let oc := runp f' (gas - c_call C) c (CODE c) rd brd nrd
                           n bn nn w cred deb in
            if o_ok oc
            then
              let o2 := runp f' (o_gas oc) cur (k true) rd brd nrd
                             (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                             (o_cred oc) (o_deb oc) in
              Out (o_slog oc ++ o_slog o2) (o_blog oc ++ o_blog o2)
                  (o_nlog oc ++ o_nlog o2) (o_buf o2)
                  (o_evs oc ++ o_evs o2) (o_tvs oc ++ o_tvs o2)
                  (o_ok o2) (o_gas o2) (o_ref oc + o_ref o2)
                  (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
            else
              let o2 := runp f' (o_gas oc) cur (k false) rd brd nrd
                             (o_n oc) (o_bn oc) (o_nn oc) w cred deb in
              Out (o_slog oc ++ o_slog o2) (o_blog oc ++ o_blog o2)
                  (o_nlog oc ++ o_nlog o2) (o_buf o2)
                  (o_evs o2) (o_tvs o2)
                  (o_ok o2) (o_gas o2) (o_ref o2)
                  (o_cred o2) (o_deb o2) (o_n o2) (o_bn o2) (o_nn o2)
          else oog gas w cred deb n bn nn
      end
  end.

(** Case-split helper for goals over [runp]: splits the pending gas checks,
    buffer lookups, and branch tests that guard each execution case. *)

Ltac rsplit :=
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b eqn:?
  | |- context [match wlookup ?w ?k with _ => _ end] =>
      destruct (wlookup w k) eqn:?
  end.

(** A transaction runs with fuel equal to its gas limit, at its fee account,
    with fresh ordinals, an empty overlay, no credits, and the upfront hold
    of its whole gas cost against its fee account. *)

Definition deb0 (fee : addr) (hold : nat) : addr -> nat :=
  fun a => if a =? fee then hold else 0.

Definition zerof : addr -> nat := fun _ => 0.

Definition runt (i : item) (rd : reader) (brd : breader) (nrd : nreader) : out :=
  let '(fee, t, g, p) := i in
  runp g g fee t rd brd nrd 0 0 0 [] zerof (deb0 fee (g * p)).

(** ** Receipts, the gated step, sequential execution

    The gate is checked against the true prefix bank before any execution:
    a rejected transaction performs no run and leaves the machine untouched.
    An executed transaction holds its whole gas cost, settles its recorded
    transfers, returns the unconsumed and refunded portion, pays the
    consumed portion to the coinbase, and bumps its nonce.  A reverted
    transaction pays for what it consumed with no refund. *)

Definition mach : Type := (storage * bank * nonces)%type.

Inductive status : Type := SOk | SRev | SRejected.

Definition rcpt : Type :=
  (status * nat * buffer * list val * list transfer)%type.

Definition finish (st : storage) (bk : bank) (nm : nonces)
                  (fee : addr) (g p : nat) (o : out) : mach * rcpt :=
  let u := g - o_gas o in
  if o_ok o
  then
    let u_eff := u - Nat.min (o_ref o) (u / 2) in
    let b1 := bupd bk fee (bk fee - g * p) in
    let b2 := apply_tvs b1 (o_tvs o) in
    let b3 := bupd b2 fee (b2 fee + (g - u_eff) * p) in
    let b4 := bupd b3 CB (b3 CB + u_eff * p) in
    ((commit st (o_buf o), b4, bupd nm fee (S (nm fee))),
     (SOk, u_eff, o_buf o, o_evs o, o_tvs o))
  else
    ((st, bupd (bupd bk fee (bk fee - u * p)) CB
               (bupd bk fee (bk fee - u * p) CB + u * p),
      bupd nm fee (S (nm fee))),
     (SRev, u, [], [], [])).

Definition step (m : mach) (i : item) : mach * rcpt :=
  let '(st, bk, nm) := m in
  let '(fee, t, g, p) := i in
  if g * p <=? bk fee
  then finish st bk nm fee g p (runt i (of_state st) (of_bank bk) (of_nonces nm))
  else (m, (SRejected, 0, [], [], [])).

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

(** ** Validation and merge

    A speculation is a triple of read sources.  The merge checks the gate
    against the true prefix bank first: a rejected transaction consumes no
    execution at all.  Otherwise the storage log is validated against the
    merged prefix storage, the balance log against the merged prefix bank,
    the nonce log against the merged prefix nonces; agreement commits the
    speculative outcome unchanged, disagreement re-executes against the
    true prefix state. *)

Definition spec : Type := (reader * breader * nreader)%type.

Fixpoint omerge (m : mach) (ts : list item) (specs : list spec)
  : mach * list rcpt * nat :=
  match ts with
  | [] => (m, [], 0)
  | i :: rest =>
      let '(st, bk, nm) := m in
      let '(fee, t, g, p) := i in
      if g * p <=? bk fee
      then
        match specs with
        | (rd, brd, nrd) :: sps =>
            let o := runt i rd brd nrd in
            if valid st (o_slog o) && bvalid bk (o_blog o)
               && nvalid nm (o_nlog o)
            then
              let '(m1, r) := finish st bk nm fee g p o in
              let '(m2, rs, cnt) := omerge m1 rest sps in
              (m2, r :: rs, cnt)
            else
              let '(m1, r) := step m i in
              let '(m2, rs, cnt) := omerge m1 rest sps in
              (m2, r :: rs, S cnt)
        | [] =>
            let '(m1, r) := step m i in
            let '(m2, rs, cnt) := omerge m1 rest [] in
            (m2, r :: rs, S cnt)
        end
      else
        let '(m2, rs, cnt) := omerge m rest (tl specs) in
        (m2, (SRejected, 0, [], [], []) :: rs, cnt)
  end.

(** ** Gas bound *)

Lemma runp_gas_bound :
  forall f gas cur t rd brd nrd n bn nn w cred deb,
    o_gas (runp f gas cur t rd brd nrd n bn nn w cred deb) <= gas.
Proof.
  induction f as [| f' IH]; intros gas cur t rd brd nrd n bn nn w cred deb;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    simpl; try lia; rsplit; simpl; try lia;
    try (eapply Nat.le_trans; [apply IH | lia]);
    (eapply Nat.le_trans; [apply IH |];
     eapply Nat.le_trans; [apply IH | lia]).
Qed.

(** ** Replay

    A storage, bank, and nonce map agreeing with every logged read
    reproduce a run exactly: logs, buffer, events, transfers, revert
    decision, gas, refunds, deltas, and ordinals, whatever the read
    sources were.  Buffer hits, in-flight arithmetic, and frame decisions
    are functions of the logged values, so agreement on the logs pins the
    whole run. *)

Lemma replay :
  forall f gas cur t rd brd nrd n bn nn w cred deb
         (s : storage) (b : bank) (nm : nonces),
    (forall k v, In (k, v) (o_slog (runp f gas cur t rd brd nrd n bn nn w cred deb)) -> s k = v) ->
    (forall a v, In (a, v) (o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb)) -> b a = v) ->
    (forall a v, In (a, v) (o_nlog (runp f gas cur t rd brd nrd n bn nn w cred deb)) -> nm a = v) ->
    runp f gas cur t (of_state s) (of_bank b) (of_nonces nm) n bn nn w cred deb
    = runp f gas cur t rd brd nrd n bn nn w cred deb.
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb s b nm Hs Hb Hn;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    try reflexivity; simpl in *.
  - (* TWrite *)
    destruct (c_write C <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    rewrite (IH (gas - c_write C) cur k rd brd nrd n bn nn
                (((cur, a), v) :: w) cred deb s b nm Hs Hb Hn).
    reflexivity.
  - (* TRead *)
    destruct (c_read C <=? gas) eqn:Hg; [| reflexivity].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + simpl in Hs, Hb, Hn.
      apply (IH (gas - c_read C) cur (k v0) rd brd nrd n bn nn w cred deb s b nm
                Hs Hb Hn).
    + simpl in Hs, Hb, Hn.
      assert (Hv : s (cur, a) = rd n (cur, a))
        by (apply Hs; left; reflexivity).
      replace (of_state s n (cur, a)) with (rd n (cur, a))
        by (symmetry; exact Hv).
      assert (Hs' : forall k0 v0,
                 In (k0, v0)
                    (o_slog (runp f' (gas - c_read C) cur (k (rd n (cur, a)))
                                  rd brd nrd (S n) bn nn w cred deb)) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. right. exact Hin. }
      rewrite (IH (gas - c_read C) cur (k (rd n (cur, a))) rd brd nrd
                  (S n) bn nn w cred deb s b nm Hs' Hb Hn).
      reflexivity.
  - (* TBal *)
    destruct (c_bal C <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    assert (Hv : b a = brd bn a) by (apply Hb; left; reflexivity).
    replace (of_bank b bn a) with (brd bn a) by (symmetry; exact Hv).
    assert (Hb' : forall a0 v0,
               In (a0, v0)
                  (o_blog (runp f' (gas - c_bal C) cur
                                (k (brd bn a + cred a - deb a))
                                rd brd nrd n (S bn) nn w cred deb)) ->
               b a0 = v0).
    { intros a0 v0 Hin. apply Hb. right. exact Hin. }
    rewrite (IH (gas - c_bal C) cur (k (brd bn a + cred a - deb a)) rd brd nrd
                n (S bn) nn w cred deb s b nm Hs Hb' Hn).
    reflexivity.
  - (* TNonce *)
    destruct (c_nonce C <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    assert (Hv : nm a = nrd nn a) by (apply Hn; left; reflexivity).
    replace (of_nonces nm nn a) with (nrd nn a) by (symmetry; exact Hv).
    assert (Hn' : forall a0 v0,
               In (a0, v0)
                  (o_nlog (runp f' (gas - c_nonce C) cur (k (nrd nn a))
                                rd brd nrd n bn (S nn) w cred deb)) ->
               nm a0 = v0).
    { intros a0 v0 Hin. apply Hn. right. exact Hin. }
    rewrite (IH (gas - c_nonce C) cur (k (nrd nn a)) rd brd nrd
                n bn (S nn) w cred deb s b nm Hs Hb Hn').
    reflexivity.
  - (* TWhile *)
    destruct (c_while C <=? gas) eqn:Hg; [| reflexivity].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw.
    + simpl in Hs, Hb, Hn.
      destruct (v0 =? 0) eqn:Hz.
      * apply (IH (gas - c_while C) cur k rd brd nrd n bn nn w cred deb s b nm
                  Hs Hb Hn).
      * apply (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                  n bn nn w cred deb s b nm Hs Hb Hn).
    + simpl in Hs, Hb, Hn.
      assert (Hv : s (cur, a) = rd n (cur, a))
        by (apply Hs; left; reflexivity).
      replace (of_state s n (cur, a)) with (rd n (cur, a))
        by (symmetry; exact Hv).
      assert (Hs' : forall k0 v0,
                 In (k0, v0)
                    (o_slog (if rd n (cur, a) =? 0
                             then runp f' (gas - c_while C) cur k rd brd nrd
                                       (S n) bn nn w cred deb
                             else runp f' (gas - c_while C) cur
                                       (tseq tb (TWhile a tb k)) rd brd nrd
                                       (S n) bn nn w cred deb)) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. right. exact Hin. }
      destruct (rd n (cur, a) =? 0) eqn:Hz.
      * rewrite (IH (gas - c_while C) cur k rd brd nrd
                    (S n) bn nn w cred deb s b nm Hs' Hb Hn).
        reflexivity.
      * rewrite (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                    (S n) bn nn w cred deb s b nm Hs' Hb Hn).
        reflexivity.
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg; [| reflexivity].
    simpl in Hs, Hb, Hn.
    rewrite (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb s b nm
                Hs Hb Hn).
    reflexivity.
  - (* TPay *)
    destruct (c_pay C <=? gas) eqn:Hg; [| reflexivity].
    assert (Hv : b cur = brd bn cur).
    { apply Hb.
      destruct (amt <=? brd bn cur + cred cur - deb cur); simpl; left; reflexivity. }
    replace (of_bank b bn cur) with (brd bn cur) by (symmetry; exact Hv).
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp;
      simpl in Hs, Hb, Hn.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - c_pay C) cur (k true) rd brd nrd
                                  n (S bn) nn w
                                  (bupd cred d (cred d + amt))
                                  (bupd deb cur (deb cur + amt)))) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      rewrite (IH (gas - c_pay C) cur (k true) rd brd nrd n (S bn) nn w
                  (bupd cred d (cred d + amt)) (bupd deb cur (deb cur + amt))
                  s b nm Hs Hb' Hn).
      reflexivity.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - c_pay C) cur (k false) rd brd nrd
                                  n (S bn) nn w cred deb)) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      rewrite (IH (gas - c_pay C) cur (k false) rd brd nrd n (S bn) nn w
                  cred deb s b nm Hs Hb' Hn).
      reflexivity.
  - (* TCall *)
    destruct (c_call C <=? gas) eqn:Hg; [| reflexivity].
    set (oc := runp f' (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb)
      in *.
    destruct (o_ok oc) eqn:Hok; simpl in Hs, Hb, Hn.
    + assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
      { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
      assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
      assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
      { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
      assert (Ec : runp f' (gas - c_call C) c (CODE c)
                        (of_state s) (of_bank b) (of_nonces nm)
                        n bn nn w cred deb = oc).
      { apply (IH (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb
                  s b nm Hsc Hbc Hnc). }
      rewrite Ec, Hok.
      assert (Hs2 : forall k0 v0,
                 In (k0, v0)
                    (o_slog (runp f' (o_gas oc) cur (k true) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                                  (o_cred oc) (o_deb oc))) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
      assert (Hb2 : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (o_gas oc) cur (k true) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                                  (o_cred oc) (o_deb oc))) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
      assert (Hn2 : forall a0 v0,
                 In (a0, v0)
                    (o_nlog (runp f' (o_gas oc) cur (k true) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                                  (o_cred oc) (o_deb oc))) ->
                 nm a0 = v0).
      { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
      rewrite (IH (o_gas oc) cur (k true) rd brd nrd (o_n oc) (o_bn oc)
                  (o_nn oc) (o_buf oc) (o_cred oc) (o_deb oc) s b nm
                  Hs2 Hb2 Hn2).
      reflexivity.
    + assert (Hsc : forall k0 v0, In (k0, v0) (o_slog oc) -> s k0 = v0).
      { intros k0 v0 Hin. apply Hs. apply in_or_app. left. exact Hin. }
      assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> b a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
      assert (Hnc : forall a0 v0, In (a0, v0) (o_nlog oc) -> nm a0 = v0).
      { intros a0 v0 Hin. apply Hn. apply in_or_app. left. exact Hin. }
      assert (Ec : runp f' (gas - c_call C) c (CODE c)
                        (of_state s) (of_bank b) (of_nonces nm)
                        n bn nn w cred deb = oc).
      { apply (IH (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb
                  s b nm Hsc Hbc Hnc). }
      rewrite Ec, Hok.
      assert (Hs2 : forall k0 v0,
                 In (k0, v0)
                    (o_slog (runp f' (o_gas oc) cur (k false) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) w cred deb)) ->
                 s k0 = v0).
      { intros k0 v0 Hin. apply Hs. apply in_or_app. right. exact Hin. }
      assert (Hb2 : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (o_gas oc) cur (k false) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) w cred deb)) ->
                 b a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
      assert (Hn2 : forall a0 v0,
                 In (a0, v0)
                    (o_nlog (runp f' (o_gas oc) cur (k false) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) w cred deb)) ->
                 nm a0 = v0).
      { intros a0 v0 Hin. apply Hn. apply in_or_app. right. exact Hin. }
      rewrite (IH (o_gas oc) cur (k false) rd brd nrd (o_n oc) (o_bn oc)
                  (o_nn oc) w cred deb s b nm Hs2 Hb2 Hn2).
      reflexivity.
Qed.

(** ** Self-validation, one source at a time *)

Lemma valid_self_s :
  forall f gas cur t (s : storage) brd nrd n bn nn w cred deb,
    valid s (o_slog (runp f gas cur t (of_state s) brd nrd n bn nn w cred deb))
    = true.
Proof.
  induction f as [| f' IH]; intros gas cur t s brd nrd n bn nn w cred deb;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; apply IH);
    (rewrite valid_app; rewrite !IH; reflexivity).
Qed.

Lemma bvalid_self_b :
  forall f gas cur t rd (b : bank) nrd n bn nn w cred deb,
    bvalid b (o_blog (runp f gas cur t rd (of_bank b) nrd n bn nn w cred deb))
    = true.
Proof.
  induction f as [| f' IH]; intros gas cur t rd b nrd n bn nn w cred deb;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; apply IH);
    (rewrite bvalid_app; rewrite !IH; reflexivity).
Qed.

Lemma nvalid_self_n :
  forall f gas cur t rd brd (nm : nonces) n bn nn w cred deb,
    nvalid nm (o_nlog (runp f gas cur t rd brd (of_nonces nm) n bn nn w cred deb))
    = true.
Proof.
  unfold nvalid.
  induction f as [| f' IH]; intros gas cur t rd brd nm n bn nn w cred deb;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    simpl; rsplit; simpl;
    try reflexivity;
    try (apply IH);
    try (rewrite Nat.eqb_refl; simpl; apply IH);
    (rewrite bvalid_app; rewrite !IH; reflexivity).
Qed.

(** ** In-flight settlement soundness

    Along any run whose logged balance reads agree with a bank [B], the
    in-flight discipline is exact: the recorded transfers settle stepwise
    against the tracked bank without truncation, and settlement lands on
    the bank described by the final deltas.  The invariant is stated
    additively, so nat subtraction never bites. *)

Definition inflight_inv (B bc : bank) (cred deb : addr -> nat) : Prop :=
  forall a, bc a + deb a = B a + cred a.

Lemma inflight_sound :
  forall f gas cur t rd brd nrd n bn nn w cred deb (B bc : bank),
    (forall a v, In (a, v) (o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb)) -> B a = v) ->
    inflight_inv B bc cred deb ->
    apply_ok bc (o_tvs (runp f gas cur t rd brd nrd n bn nn w cred deb)) = true
    /\ inflight_inv B
         (apply_tvs bc (o_tvs (runp f gas cur t rd brd nrd n bn nn w cred deb)))
         (o_cred (runp f gas cur t rd brd nrd n bn nn w cred deb))
         (o_deb (runp f gas cur t rd brd nrd n bn nn w cred deb)).
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb B bc Hb Hinv;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    simpl in *;
    try (split; [reflexivity | exact Hinv]).
  - (* TWrite *)
    destruct (c_write C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    apply (IH (gas - c_write C) cur k rd brd nrd n bn nn
              (((cur, a), v) :: w) cred deb B bc Hb Hinv).
  - (* TRead *)
    destruct (c_read C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw; simpl in Hb.
    + apply (IH (gas - c_read C) cur (k v0) rd brd nrd n bn nn w cred deb
                B bc Hb Hinv).
    + apply (IH (gas - c_read C) cur (k (rd n (cur, a))) rd brd nrd
                (S n) bn nn w cred deb B bc Hb Hinv).
  - (* TBal *)
    destruct (c_bal C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    assert (Hb' : forall a0 v0,
               In (a0, v0)
                  (o_blog (runp f' (gas - c_bal C) cur
                                (k (brd bn a + cred a - deb a))
                                rd brd nrd n (S bn) nn w cred deb)) ->
               B a0 = v0).
    { intros a0 v0 Hin. apply Hb. right. exact Hin. }
    apply (IH (gas - c_bal C) cur (k (brd bn a + cred a - deb a)) rd brd nrd
              n (S bn) nn w cred deb B bc Hb' Hinv).
  - (* TNonce *)
    destruct (c_nonce C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    apply (IH (gas - c_nonce C) cur (k (nrd nn a)) rd brd nrd
              n bn (S nn) w cred deb B bc Hb Hinv).
  - (* TWhile *)
    destruct (c_while C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hw; simpl in Hb.
    + destruct (v0 =? 0) eqn:Hz.
      * apply (IH (gas - c_while C) cur k rd brd nrd n bn nn w cred deb
                  B bc Hb Hinv).
      * apply (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                  n bn nn w cred deb B bc Hb Hinv).
    + destruct (rd n (cur, a) =? 0) eqn:Hz.
      * apply (IH (gas - c_while C) cur k rd brd nrd (S n) bn nn w cred deb
                  B bc Hb Hinv).
      * apply (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                  (S n) bn nn w cred deb B bc Hb Hinv).
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    simpl in Hb.
    apply (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb B bc Hb Hinv).
  - (* TPay *)
    destruct (c_pay C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    assert (HB : B cur = brd bn cur).
    { apply Hb.
      destruct (amt <=? brd bn cur + cred cur - deb cur); simpl; left; reflexivity. }
    destruct (amt <=? brd bn cur + cred cur - deb cur) eqn:Hp; simpl in Hb.
    + apply Nat.leb_le in Hp.
      assert (Hbcur : bc cur = brd bn cur + cred cur - deb cur).
      { pose proof (Hinv cur) as Hc. rewrite HB in Hc. lia. }
      assert (Hamt : amt <= bc cur) by lia.
      assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - c_pay C) cur (k true) rd brd nrd
                                  n (S bn) nn w
                                  (bupd cred d (cred d + amt))
                                  (bupd deb cur (deb cur + amt)))) ->
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
      destruct (IH (gas - c_pay C) cur (k true) rd brd nrd n (S bn) nn w
                   (bupd cred d (cred d + amt)) (bupd deb cur (deb cur + amt))
                   B (bupd (bupd bc cur (bc cur - amt)) d
                           (bupd bc cur (bc cur - amt) d + amt))
                   Hb' Hinv') as [Hok2 Hinv2].
      split.
      * simpl. apply andb_true_iff. split; [apply Nat.leb_le; exact Hamt |].
        exact Hok2.
      * simpl. exact Hinv2.
    + assert (Hb' : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (gas - c_pay C) cur (k false) rd brd nrd
                                  n (S bn) nn w cred deb)) ->
                 B a0 = v0).
      { intros a0 v0 Hin. apply Hb. right. exact Hin. }
      apply (IH (gas - c_pay C) cur (k false) rd brd nrd n (S bn) nn w
                cred deb B bc Hb' Hinv).
  - (* TCall *)
    destruct (c_call C <=? gas) eqn:Hg;
      [| split; [reflexivity | exact Hinv]].
    set (oc := runp f' (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb)
      in *.
    destruct (o_ok oc) eqn:Hok; simpl in Hb.
    + assert (Hbc : forall a0 v0, In (a0, v0) (o_blog oc) -> B a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. left. exact Hin. }
      destruct (IH (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb
                   B bc Hbc Hinv) as [Hokc Hinvc].
      fold oc in Hokc, Hinvc.
      assert (Hb2 : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (o_gas oc) cur (k true) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) (o_buf oc)
                                  (o_cred oc) (o_deb oc))) ->
                 B a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
      destruct (IH (o_gas oc) cur (k true) rd brd nrd (o_n oc) (o_bn oc)
                   (o_nn oc) (o_buf oc) (o_cred oc) (o_deb oc)
                   B (apply_tvs bc (o_tvs oc)) Hb2 Hinvc) as [Hok2 Hinv2].
      split.
      * simpl. rewrite apply_ok_app. apply andb_true_iff. split; [exact Hokc |].
        exact Hok2.
      * simpl. rewrite apply_app. exact Hinv2.
    + assert (Hb2 : forall a0 v0,
                 In (a0, v0)
                    (o_blog (runp f' (o_gas oc) cur (k false) rd brd nrd
                                  (o_n oc) (o_bn oc) (o_nn oc) w cred deb)) ->
                 B a0 = v0).
      { intros a0 v0 Hin. apply Hb. apply in_or_app. right. exact Hin. }
      apply (IH (o_gas oc) cur (k false) rd brd nrd (o_n oc) (o_bn oc)
                (o_nn oc) w cred deb B bc Hb2 Hinv).
Qed.

(** ** Replay at the transaction level *)

Lemma replay_runt :
  forall i rd brd nrd (st : storage) (bk : bank) (nm : nonces),
    valid st (o_slog (runt i rd brd nrd)) = true ->
    bvalid bk (o_blog (runt i rd brd nrd)) = true ->
    nvalid nm (o_nlog (runt i rd brd nrd)) = true ->
    runt i (of_state st) (of_bank bk) (of_nonces nm) = runt i rd brd nrd.
Proof.
  intros [[[fee t] g] p] rd brd nrd st bk nm Hv Hb Hn.
  unfold runt in *.
  apply replay.
  - exact (valid_true_In _ _ Hv).
  - exact (bvalid_true_In _ _ Hb).
  - exact (bvalid_true_In _ _ Hn).
Qed.

(** ** Main theorem: merged execution is sequential execution *)

Theorem optimistic_correct :
  forall ts specs m,
    fst (omerge m ts specs) = seq_execr m ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - reflexivity.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps]; cbn [omerge seq_execr tl].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omerge m1 rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] m1). rewrite E in HI. cbn [fst] in HI.
        cbn [fst]. rewrite <- HI.
        reflexivity.
      * assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                        = ((st, bk, nm), (SRejected, 0, [], [], []))).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        destruct (omerge (st, bk, nm) rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] (st, bk, nm)). rewrite E in HI. cbn [fst] in HI.
        cbn [fst]. rewrite <- HI.
        reflexivity.
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) rd brd nrd) in *.
        destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- apply andb_true_iff in Ev. destruct Ev as [Ev1 Evn].
           apply andb_true_iff in Ev1. destruct Ev1 as [Evs Evb].
           assert (Ho : runt (fee, t, g, p) (of_state st) (of_bank bk)
                             (of_nonces nm) = o).
           { unfold o. apply replay_runt; assumption. }
           assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                           = finish st bk nm fee g p o).
           { unfold step. rewrite Hgate. rewrite Ho. reflexivity. }
           rewrite Hstep.
           destruct (finish st bk nm fee g p o) as [m1 r].
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite E in HI. cbn [fst] in HI.
           cbn [fst]. rewrite <- HI.
           reflexivity.
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite E in HI. cbn [fst] in HI.
           cbn [fst]. rewrite <- HI.
           reflexivity.
      * destruct (omerge (st, bk, nm) rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps (st, bk, nm)). rewrite E in HI. cbn [fst] in HI.
        assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                        = ((st, bk, nm), (SRejected, 0, [], [], []))).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        cbn [fst]. rewrite <- HI.
        reflexivity.
Qed.

(** ** The perfect-speculation fast path *)

Fixpoint prefix_specs (m : mach) (ts : list item) : list spec :=
  match ts with
  | [] => []
  | i :: rest =>
      (of_state (fst (fst m)), of_bank (snd (fst m)), of_nonces (snd m))
        :: prefix_specs (fst (step m i)) rest
  end.

Theorem fast_path :
  forall ts m,
    omerge m ts (prefix_specs m ts) = (seq_execr m ts, 0).
Proof.
  induction ts as [| i rest IH]; intros m.
  - reflexivity.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    cbn [omerge seq_execr prefix_specs tl fst snd].
    destruct (g * p <=? bk fee) eqn:Hgate.
    + set (o := runt (fee, t, g, p) (of_state st) (of_bank bk) (of_nonces nm))
        in *.
      assert (Evs : valid st (o_slog o) = true).
      { unfold o, runt. apply valid_self_s. }
      assert (Evb : bvalid bk (o_blog o) = true).
      { unfold o, runt. apply bvalid_self_b. }
      assert (Evn : nvalid nm (o_nlog o) = true).
      { unfold o, runt. apply nvalid_self_n. }
      rewrite Evs, Evb, Evn. cbn [andb].
      assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = finish st bk nm fee g p o).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (finish st bk nm fee g p o) as [m1 r].
      cbn [fst].
      rewrite (IH m1).
      destruct (seq_execr m1 rest) as [m2 rs].
      reflexivity.
    + assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = ((st, bk, nm), (SRejected, 0, [], [], []))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      cbn [fst].
      rewrite (IH (st, bk, nm)).
      destruct (seq_execr (st, bk, nm) rest) as [m2 rs].
      reflexivity.
Qed.

(** ** Aggregate re-execution bound *)

Theorem reexec_bound :
  forall ts specs m,
    snd (omerge m ts specs) <= length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps]; cbn [omerge length tl].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omerge m1 rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] m1). rewrite E in HI. cbn [snd] in HI.
        cbn [snd]. lia.
      * destruct (omerge (st, bk, nm) rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] (st, bk, nm)). rewrite E in HI. cbn [snd] in HI.
        cbn [snd]. lia.
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) rd brd nrd).
        destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- destruct (finish st bk nm fee g p o) as [m1 r].
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite E in HI. cbn [snd] in HI.
           cbn [snd]. lia.
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite E in HI. cbn [snd] in HI.
           cbn [snd]. lia.
      * destruct (omerge (st, bk, nm) rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps (st, bk, nm)). rewrite E in HI. cbn [snd] in HI.
        cbn [snd]. lia.
Qed.

(** ** Speculation independence and scheduler safety *)

Corollary speculation_irrelevant :
  forall ts specs1 specs2 m,
    fst (omerge m ts specs1) = fst (omerge m ts specs2).
Proof.
  intros ts specs1 specs2 m.
  rewrite (optimistic_correct ts specs1 m).
  rewrite (optimistic_correct ts specs2 m).
  reflexivity.
Qed.

(** ** Instrumented merge: per-position flags and the operational run count

    [omergeX] mirrors [omerge] and additionally returns one boolean per
    position, true exactly when that position re-executed, and the count of
    [runp] invocations the merge performs: one per validated speculation,
    two per conflicted position, one per position whose speculation is
    missing, none for a rejected transaction. *)

Fixpoint omergeX (m : mach) (ts : list item) (specs : list spec)
  : mach * list rcpt * list bool * nat :=
  match ts with
  | [] => (m, [], [], 0)
  | i :: rest =>
      let '(st, bk, nm) := m in
      let '(fee, t, g, p) := i in
      if g * p <=? bk fee
      then
        match specs with
        | (rd, brd, nrd) :: sps =>
            let o := runt i rd brd nrd in
            if valid st (o_slog o) && bvalid bk (o_blog o)
               && nvalid nm (o_nlog o)
            then
              let '(m1, r) := finish st bk nm fee g p o in
              let '(m2, rs, fl, k) := omergeX m1 rest sps in
              (m2, r :: rs, false :: fl, S k)
            else
              let '(m1, r) := step m i in
              let '(m2, rs, fl, k) := omergeX m1 rest sps in
              (m2, r :: rs, true :: fl, S (S k))
        | [] =>
            let '(m1, r) := step m i in
            let '(m2, rs, fl, k) := omergeX m1 rest [] in
            (m2, r :: rs, true :: fl, S k)
        end
      else
        let '(m2, rs, fl, k) := omergeX m rest (tl specs) in
        (m2, (SRejected, 0, [], [], []) :: rs, false :: fl, k)
  end.

Definition executions (m : mach) (ts : list item) (specs : list spec) : nat :=
  snd (omergeX m ts specs).

Definition reexec_flags (m : mach) (ts : list item) (specs : list spec)
  : list bool :=
  snd (fst (omergeX m ts specs)).

Fixpoint count_true (l : list bool) : nat :=
  match l with
  | [] => 0
  | b :: r => (if b then 1 else 0) + count_true r
  end.

Lemma omergeX_omerge :
  forall ts specs m,
    fst (fst (omergeX m ts specs)) = fst (omerge m ts specs)
    /\ count_true (snd (fst (omergeX m ts specs))) = snd (omerge m ts specs)
    /\ length (snd (fst (omergeX m ts specs))) = length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. auto.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps]; cbn [omergeX omerge length tl].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omergeX m1 rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge m1 rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] m1). rewrite EX, E in HI. cbn in HI.
        destruct HI as [H1 [H2 H3]]. injection H1 as -> ->.
        cbn. split; [reflexivity | split; lia].
      * destruct (omergeX (st, bk, nm) rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge (st, bk, nm) rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] (st, bk, nm)). rewrite EX, E in HI. cbn in HI.
        destruct HI as [H1 [H2 H3]]. injection H1 as -> ->.
        cbn. split; [reflexivity | split; lia].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) rd brd nrd).
        destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- destruct (finish st bk nm fee g p o) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite EX, E in HI. cbn in HI.
           destruct HI as [H1 [H2 H3]]. injection H1 as -> ->.
           cbn. split; [reflexivity | split; lia].
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite EX, E in HI. cbn in HI.
           destruct HI as [H1 [H2 H3]]. injection H1 as -> ->.
           cbn. split; [reflexivity | split; lia].
      * destruct (omergeX (st, bk, nm) rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge (st, bk, nm) rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps (st, bk, nm)). rewrite EX, E in HI. cbn in HI.
        destruct HI as [H1 [H2 H3]]. injection H1 as -> ->.
        cbn. split; [reflexivity | split; lia].
Qed.

(** Each position re-executes at most once: the re-execution count is a sum
    of one boolean per position. *)

Theorem reexec_per_tx :
  forall ts specs m,
    snd (omerge m ts specs) = count_true (reexec_flags m ts specs)
    /\ length (reexec_flags m ts specs) = length ts.
Proof.
  intros ts specs m. unfold reexec_flags.
  destruct (omergeX_omerge ts specs m) as [_ [H2 H3]].
  split; [symmetry; exact H2 | exact H3].
Qed.

(** ** Work accounting

    [executions] counts actual [runp] invocations.  The law: with a full
    speculation vector, the merge runs each non-rejected transaction once,
    plus once more per re-execution; and unconditionally the work is
    bounded by twice the block length and below by the non-rejected
    count. *)

Definition is_rejected (r : rcpt) : bool :=
  match fst (fst (fst (fst r))) with
  | SRejected => true
  | _ => false
  end.

Definition nonrejected (rs : list rcpt) : nat :=
  length (filter (fun r => negb (is_rejected r)) rs).

Lemma finish_not_rejected :
  forall st bk nm fee g p o,
    is_rejected (snd (finish st bk nm fee g p o)) = false.
Proof.
  intros. unfold finish. destruct (o_ok o); reflexivity.
Qed.

Lemma step_gate_finish :
  forall st bk nm fee t g p,
    g * p <=? bk fee = true ->
    step (st, bk, nm) (fee, t, g, p)
    = finish st bk nm fee g p
             (runt (fee, t, g, p) (of_state st) (of_bank bk) (of_nonces nm)).
Proof.
  intros st bk nm fee t g p Hg. unfold step. rewrite Hg. reflexivity.
Qed.

Theorem executions_law :
  forall ts specs m,
    length ts <= length specs ->
    executions m ts specs
    = nonrejected (snd (fst (omerge m ts specs))) + snd (omerge m ts specs).
Proof.
  induction ts as [| i rest IH]; intros specs m Hlen.
  - cbn. reflexivity.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps];
      [cbn in Hlen; lia |].
    cbn in Hlen. unfold executions in *. cbn [omergeX omerge tl].
    destruct (g * p <=? bk fee) eqn:Hgate.
    + set (o := runt (fee, t, g, p) rd brd nrd).
      destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                && nvalid nm (o_nlog o)) eqn:Ev.
      * destruct (finish st bk nm fee g p o) as [m1 r] eqn:EF.
        destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps m1 ltac:(lia)). rewrite EX, E in HI. cbn in HI.
        assert (Hnr : is_rejected r = false).
        { assert (Hf := finish_not_rejected st bk nm fee g p o).
          rewrite EF in Hf. exact Hf. }
        cbn. unfold nonrejected. cbn [filter]. rewrite Hnr. cbn [negb].
        unfold nonrejected in HI. cbn [length]. lia.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r] eqn:ES.
        destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps m1 ltac:(lia)). rewrite EX, E in HI. cbn in HI.
        assert (Hnr : is_rejected r = false).
        { rewrite step_gate_finish in ES by exact Hgate.
          assert (Hf := finish_not_rejected st bk nm fee g p
                          (runt (fee, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
          rewrite ES in Hf. exact Hf. }
        cbn. unfold nonrejected. cbn [filter]. rewrite Hnr. cbn [negb].
        unfold nonrejected in HI. cbn [length]. lia.
    + destruct (omergeX (st, bk, nm) rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
      destruct (omerge (st, bk, nm) rest sps) as [[m2 rs] cnt] eqn:E.
      assert (HI := IH sps (st, bk, nm) ltac:(lia)). rewrite EX, E in HI.
      cbn in HI.
      cbn. unfold nonrejected. cbn [filter is_rejected fst negb].
      unfold nonrejected in HI. lia.
Qed.

Theorem work_upper :
  forall ts specs m, executions m ts specs <= 2 * length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps];
      unfold executions in *; cbn [omergeX length tl].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omergeX m1 rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        assert (HI := IH [] m1). rewrite EX in HI. cbn in HI. cbn. lia.
      * destruct (omergeX (st, bk, nm) rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        assert (HI := IH [] (st, bk, nm)). rewrite EX in HI. cbn in HI.
        cbn. lia.
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) rd brd nrd).
        destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- destruct (finish st bk nm fee g p o) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           assert (HI := IH sps m1). rewrite EX in HI. cbn in HI. cbn. lia.
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           assert (HI := IH sps m1). rewrite EX in HI. cbn in HI. cbn. lia.
      * destruct (omergeX (st, bk, nm) rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
        assert (HI := IH sps (st, bk, nm)). rewrite EX in HI. cbn in HI.
        cbn. lia.
Qed.

Theorem work_lower :
  forall ts specs m,
    nonrejected (snd (fst (omerge m ts specs))) <= executions m ts specs.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps];
      unfold executions in *; cbn [omergeX omerge tl].
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omergeX m1 rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge m1 rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] m1). rewrite EX, E in HI. cbn in HI.
        cbn. unfold nonrejected. cbn [filter].
        destruct (negb (is_rejected r)); cbn [length];
          unfold nonrejected in HI; lia.
      * destruct (omergeX (st, bk, nm) rest []) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge (st, bk, nm) rest []) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH [] (st, bk, nm)). rewrite EX, E in HI. cbn in HI.
        cbn. unfold nonrejected. cbn [filter is_rejected fst negb].
        unfold nonrejected in HI. lia.
    + destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) rd brd nrd).
        destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- destruct (finish st bk nm fee g p o) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite EX, E in HI. cbn in HI.
           cbn. unfold nonrejected. cbn [filter].
           destruct (negb (is_rejected r)); cbn [length];
             unfold nonrejected in HI; lia.
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
           destruct (omergeX m1 rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
           destruct (omerge m1 rest sps) as [[m2 rs] cnt] eqn:E.
           assert (HI := IH sps m1). rewrite EX, E in HI. cbn in HI.
           cbn. unfold nonrejected. cbn [filter].
           destruct (negb (is_rejected r)); cbn [length];
             unfold nonrejected in HI; lia.
      * destruct (omergeX (st, bk, nm) rest sps) as [[[m2x rsx] flx] kx] eqn:EX.
        destruct (omerge (st, bk, nm) rest sps) as [[m2 rs] cnt] eqn:E.
        assert (HI := IH sps (st, bk, nm)). rewrite EX, E in HI. cbn in HI.
        cbn. unfold nonrejected. cbn [filter is_rejected fst negb].
        unfold nonrejected in HI. lia.
Qed.

(** ** The operational dispatch scheduler *)

Definition spec_of (m : mach) : spec :=
  (of_state (fst (fst m)), of_bank (snd (fst m)), of_nonces (snd m)).

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
  2:{ unfold dispatch. rewrite length_map, length_seq. lia. }
  rewrite dispatch_in_order. rewrite fast_path. cbn [fst snd]. lia.
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
    + destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
      cbn [prefix_specs firstn app omerge tl length fst snd].
      destruct (g * p <=? bk fee) eqn:Hgate.
      * set (o := runt (fee, t, g, p) (of_state st) (of_bank bk)
                       (of_nonces nm)) in *.
        assert (Evs : valid st (o_slog o) = true).
        { unfold o, runt. apply valid_self_s. }
        assert (Evb : bvalid bk (o_blog o) = true).
        { unfold o, runt. apply bvalid_self_b. }
        assert (Evn : nvalid nm (o_nlog o) = true).
        { unfold o, runt. apply nvalid_self_n. }
        rewrite Evs, Evb, Evn. cbn [andb].
        assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                        = finish st bk nm fee g p o).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        destruct (finish st bk nm fee g p o) as [m1 r].
        cbn [fst].
        destruct (omerge m1 rest (firstn r' (prefix_specs m1 rest) ++ sps'))
          as [[m2 rs] cnt] eqn:E.
        assert (HI := IH r' m1 sps'). rewrite E in HI. cbn [snd] in HI.
        cbn [snd]. lia.
      * assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                        = ((st, bk, nm), (SRejected, 0, [], [], []))).
        { unfold step. rewrite Hgate. reflexivity. }
        rewrite Hstep.
        cbn [fst].
        destruct (omerge (st, bk, nm) rest
                         (firstn r' (prefix_specs (st, bk, nm) rest) ++ sps'))
          as [[m2 rs] cnt] eqn:E.
        assert (HI := IH r' (st, bk, nm) sps'). rewrite E in HI.
        cbn [snd] in HI.
        cbn [snd]. lia.
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

Definition ditem : item := (0, TDone, 0, 0).

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

(** ** Money conservation

    The bank is an exact ledger across gas, coinbase, and transfers: for
    every account, final balance plus debits equals initial balance plus
    credits.  Debits are the effective gas paid by transactions the account
    sponsored plus the transfers it sent, from any frame; credits are
    coinbase gas income plus transfers received. *)

Fixpoint debits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (fee, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb fee f then u * p else 0) + outsum f tvs + debits f ts' rs'
  | _, _ => 0
  end.

Fixpoint credits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (_, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb CB f then u * p else 0) + insum f tvs + credits f ts' rs'
  | _, _ => 0
  end.

(** The bank algebra of a committing transaction: upfront hold, transfer
    settlement, refund of the unconsumed and refunded portion, coinbase
    payment.  Stated raw so the ledger proofs can cite it pointwise. *)

Lemma commit_bank_law :
  forall (bk : bank) fee g p (tvs : list transfer) ue f,
    g * p <= bk fee ->
    ue <= g ->
    apply_ok (bupd bk fee (bk fee - g * p)) tvs = true ->
    bupd (bupd (apply_tvs (bupd bk fee (bk fee - g * p)) tvs) fee
               (apply_tvs (bupd bk fee (bk fee - g * p)) tvs fee
                + (g - ue) * p)) CB
         (bupd (apply_tvs (bupd bk fee (bk fee - g * p)) tvs) fee
               (apply_tvs (bupd bk fee (bk fee - g * p)) tvs fee
                + (g - ue) * p) CB + ue * p) f
    + (if Nat.eqb fee f then ue * p else 0) + outsum f tvs
    = bk f + (if Nat.eqb CB f then ue * p else 0) + insum f tvs.
Proof.
  intros bk fee g p tvs ue f Hgle Hue Hok.
  assert (AL := apply_law tvs (bupd bk fee (bk fee - g * p)) Hok f).
  assert (Huep : ue * p <= g * p) by (apply Nat.mul_le_mono_r; lia).
  assert (Hdist : (g - ue) * p = g * p - ue * p)
    by (apply Nat.mul_sub_distr_r).
  set (b2 := apply_tvs (bupd bk fee (bk fee - g * p)) tvs) in *.
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
    g * p <= bk fee ->
    u <= g ->
    bupd (bupd bk fee (bk fee - u * p)) CB
         (bupd bk fee (bk fee - u * p) CB + u * p) f
    + (if Nat.eqb fee f then u * p else 0)
    = bk f + (if Nat.eqb CB f then u * p else 0).
Proof.
  intros bk fee g p u f Hgle Hu.
  assert (Hup : u * p <= g * p) by (apply Nat.mul_le_mono_r; lia).
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

Theorem money_conservation :
  forall ts m f,
    snd (fst (fst (seq_execr m ts))) f + debits f ts (snd (seq_execr m ts))
    = snd (fst m) f + credits f ts (snd (seq_execr m ts)).
Proof.
  induction ts as [| i rest IH]; intros m f.
  - cbn. lia.
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    cbn [seq_execr].
    destruct (g * p <=? bk fee) eqn:Hgate.
    + assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = finish st bk nm fee g p
                          (runt (fee, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      set (o := runt (fee, t, g, p) (of_state st) (of_bank bk) (of_nonces nm))
        in *.
      assert (Hgle : g * p <= bk fee) by (apply Nat.leb_le; exact Hgate).
      unfold finish. cbv zeta.
      destruct (o_ok o) eqn:Hok; cbv beta iota.
      * set (u := g - o_gas o) in *.
        set (ue := u - Nat.min (o_ref o) (u / 2)) in *.
        assert (Hbag : forall a v, In (a, v) (o_blog o) -> bk a = v).
        { apply bvalid_true_In. unfold o, runt. apply bvalid_self_b. }
        assert (Hinv0 : inflight_inv bk (bupd bk fee (bk fee - g * p))
                          zerof (deb0 fee (g * p))).
        { intros a. unfold bupd, deb0, zerof.
          destruct (Nat.eqb a fee) eqn:Haf.
          - apply Nat.eqb_eq in Haf. subst a. lia.
          - lia. }
        assert (HIS := inflight_sound g g fee t (of_state st) (of_bank bk)
                         (of_nonces nm) 0 0 0 [] zerof (deb0 fee (g * p))
                         bk (bupd bk fee (bk fee - g * p)) Hbag Hinv0).
        assert (Hokb : apply_ok (bupd bk fee (bk fee - g * p)) (o_tvs o)
                       = true)
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
    + assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = ((st, bk, nm), (SRejected, 0, [], [], []))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
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
  | (fee, _, _, _) :: ts', (stt, _, _, _, _) :: rs' =>
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
  - destruct m as [[st bk] nm]. destruct i as [[[fee t] g] p].
    cbn [seq_execr].
    destruct (g * p <=? bk fee) eqn:Hgate.
    + assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = finish st bk nm fee g p
                          (runt (fee, t, g, p) (of_state st) (of_bank bk)
                                (of_nonces nm))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      set (o := runt (fee, t, g, p) (of_state st) (of_bank bk) (of_nonces nm))
        in *.
      unfold finish. cbv zeta.
      assert (Hnm : forall f0,
                 bupd nm fee (S (nm fee)) f0
                 = nm f0 + (if Nat.eqb fee f0 then 1 else 0)).
      { intros f0. unfold bupd.
        destruct (Nat.eqb f0 fee) eqn:Hf0;
          destruct (Nat.eqb fee f0) eqn:Hf1;
          repeat match goal with
                 | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
                 | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
                 end;
          try congruence; subst; lia. }
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
    + assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = ((st, bk, nm), (SRejected, 0, [], [], []))).
      { unfold step. rewrite Hgate. reflexivity. }
      rewrite Hstep.
      destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
      cbn [fst snd execd].
      destruct (Nat.eqb fee f); cbn; lia.
Qed.

(** ** Static footprints

    [fp Fr Fw cur t] certifies, on the syntax of [t] alone, that every
    storage read of [t] running as [cur] lands in [Fr] and every write in
    [Fw], across calls, and that [t] performs no balance, pay, or nonce
    operation: the predicate simply has no rule for [TBal], [TPay], or
    [TNonce].  Conflict freedom becomes checkable without computing the
    runs it constrains. *)

Inductive fp (Fr Fw : list key) : addr -> tx -> Prop :=
| fp_done   : forall cur, fp Fr Fw cur TDone
| fp_revert : forall cur, fp Fr Fw cur TRevert
| fp_write  : forall cur a v k,
    In (cur, a) Fw -> fp Fr Fw cur k -> fp Fr Fw cur (TWrite a v k)
| fp_read   : forall cur a k,
    In (cur, a) Fr -> (forall v, fp Fr Fw cur (k v)) ->
    fp Fr Fw cur (TRead a k)
| fp_while  : forall cur a b k,
    In (cur, a) Fr -> fp Fr Fw cur b -> fp Fr Fw cur k ->
    fp Fr Fw cur (TWhile a b k)
| fp_emit   : forall cur e k, fp Fr Fw cur k -> fp Fr Fw cur (TEmit e k)
| fp_call   : forall cur c k,
    fp Fr Fw c (CODE c) -> (forall b, fp Fr Fw cur (k b)) ->
    fp Fr Fw cur (TCall c k).

Lemma fp_tseq :
  forall Fr Fw cur t1 t2,
    fp Fr Fw cur t1 -> fp Fr Fw cur t2 -> fp Fr Fw cur (tseq t1 t2).
Proof.
  intros Fr Fw cur t1 t2 H1 H2.
  induction H1; cbn [tseq]; eauto using fp.
Qed.

Lemma fp_sound :
  forall f gas cur t rd brd nrd n bn nn w cred deb Fr Fw,
    fp Fr Fw cur t ->
    (forall k, In k (map fst w) -> In k Fw) ->
    (forall k v, In (k, v)
        (o_slog (runp f gas cur t rd brd nrd n bn nn w cred deb)) -> In k Fr)
    /\ (forall k, In k (map fst
        (o_buf (runp f gas cur t rd brd nrd n bn nn w cred deb))) -> In k Fw)
    /\ o_blog (runp f gas cur t rd brd nrd n bn nn w cred deb) = []
    /\ o_nlog (runp f gas cur t rd brd nrd n bn nn w cred deb) = [].
Proof.
  induction f as [| f' IH];
    intros gas cur t rd brd nrd n bn nn w cred deb Fr Fw Hfp Hw;
    destruct t as [| | a v k | a k | a k | a k | a tb k | e k | d amt k | c k];
    inversion Hfp; subst; simpl;
    try (split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]).
  - (* TWrite *)
    destruct (c_write C <=? gas) eqn:Hg;
      [| split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]].
    apply (IH (gas - c_write C) cur k rd brd nrd n bn nn
              (((cur, a), v) :: w) cred deb Fr Fw H4).
    intros k0 Hk0. cbn in Hk0. destruct Hk0 as [<- | Hk0].
    + exact H2.
    + apply Hw. exact Hk0.
  - (* TRead *)
    destruct (c_read C <=? gas) eqn:Hg;
      [| split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]].
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hlk.
    + apply (IH (gas - c_read C) cur (k v0) rd brd nrd n bn nn w cred deb
                Fr Fw (H3 v0) Hw).
    + destruct (IH (gas - c_read C) cur (k (rd n (cur, a))) rd brd nrd
                   (S n) bn nn w cred deb Fr Fw (H3 (rd n (cur, a))) Hw)
        as [A [B [Cc D]]].
      split; [| split; [exact B | split; [exact Cc | exact D]]].
      intros k0 w0 Hin. simpl in Hin. destruct Hin as [He | Hin].
      * injection He as <- <-. exact H2.
      * exact (A k0 w0 Hin).
  - (* TWhile *)
    destruct (c_while C <=? gas) eqn:Hg;
      [| split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]].
    assert (Hun : fp Fr Fw cur (tseq tb (TWhile a tb k))).
    { apply fp_tseq; [exact H4 |]. constructor; assumption. }
    destruct (wlookup w (cur, a)) as [v0 |] eqn:Hlk.
    + destruct (v0 =? 0) eqn:Hz.
      * apply (IH (gas - c_while C) cur k rd brd nrd n bn nn w cred deb
                  Fr Fw H5 Hw).
      * apply (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                  n bn nn w cred deb Fr Fw Hun Hw).
    + destruct (rd n (cur, a) =? 0) eqn:Hz.
      * destruct (IH (gas - c_while C) cur k rd brd nrd (S n) bn nn w cred deb
                     Fr Fw H5 Hw) as [A [B [Cc D]]].
        split; [| split; [exact B | split; [exact Cc | exact D]]].
        intros k0 w0 Hin. simpl in Hin. destruct Hin as [He | Hin].
        -- injection He as <- <-. exact H3.
        -- exact (A k0 w0 Hin).
      * destruct (IH (gas - c_while C) cur (tseq tb (TWhile a tb k)) rd brd nrd
                     (S n) bn nn w cred deb Fr Fw Hun Hw) as [A [B [Cc D]]].
        split; [| split; [exact B | split; [exact Cc | exact D]]].
        intros k0 w0 Hin. simpl in Hin. destruct Hin as [He | Hin].
        -- injection He as <- <-. exact H3.
        -- exact (A k0 w0 Hin).
  - (* TEmit *)
    destruct (c_emit C <=? gas) eqn:Hg;
      [| split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]].
    apply (IH (gas - c_emit C) cur k rd brd nrd n bn nn w cred deb Fr Fw
              H1 Hw).
  - (* TCall *)
    destruct (c_call C <=? gas) eqn:Hg;
      [| split; [intros k0 v0 Hin; destruct Hin |
                 split; [exact Hw | split; reflexivity]]].
    set (oc := runp f' (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb)
      in *.
    destruct (IH (gas - c_call C) c (CODE c) rd brd nrd n bn nn w cred deb
                 Fr Fw H2 Hw) as [A1 [B1 [C1 D1]]].
    fold oc in A1, B1, C1, D1.
    destruct (o_ok oc) eqn:Hok.
    + destruct (IH (o_gas oc) cur (k true) rd brd nrd (o_n oc) (o_bn oc)
                   (o_nn oc) (o_buf oc) (o_cred oc) (o_deb oc) Fr Fw
                   (H3 true) B1) as [A2 [B2 [C2 D2]]].
      split; [| split; [exact B2 |]].
      * intros k0 v0 Hin. simpl in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)].
      * split; simpl; [rewrite C1, C2 | rewrite D1, D2]; reflexivity.
    + destruct (IH (o_gas oc) cur (k false) rd brd nrd (o_n oc) (o_bn oc)
                   (o_nn oc) w cred deb Fr Fw (H3 false) Hw)
        as [A2 [B2 [C2 D2]]].
      split; [| split; [exact B2 |]].
      * intros k0 v0 Hin. simpl in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [exact (A1 k0 v0 Hin) | exact (A2 k0 v0 Hin)].
      * split; simpl; [rewrite C1, C2 | rewrite D1, D2]; reflexivity.
Qed.

(** ** Statically certified conflict freedom *)

Definition fp_item (Fr Fw : list key) (i : item) : Prop :=
  let '(fee, t, g, p) := i in fp Fr Fw fee t.

Definition disjoint (xs ys : list key) : Prop :=
  forall k, In k xs -> In k ys -> False.

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

Lemma static_go :
  forall ts (FRs FWs : list (list key)) (st0 : storage)
         (brd0 : breader) (nrd0 : nreader)
         (stp : storage) (bkp : bank) (nmp : nonces) (W : list key),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    (forall j FRj, nth_error FRs j = Some FRj -> disjoint W FRj) ->
    (forall k, ~ In k W -> stp k = st0 k) ->
    snd (omerge (stp, bkp, nmp) ts
                (map (fun _ => (of_state st0, brd0, nrd0)) ts)) = 0.
Proof.
  induction ts as [| i rest IH];
    intros FRs FWs st0 brd0 nrd0 stp bkp nmp W HlenR HlenW Hcert Hdisj HW Hag.
  - reflexivity.
  - destruct FRs as [| FR FRs']; [cbn in HlenR; discriminate |].
    destruct FWs as [| FW FWs']; [cbn in HlenW; discriminate |].
    cbn [length] in HlenR, HlenW.
    injection HlenR as HlenR. injection HlenW as HlenW.
    destruct i as [[[fee t] g] p].
    assert (Hfp : fp FR FW fee t).
    { assert (Hh := Hcert 0 (fee, t, g, p) FR FW eq_refl eq_refl eq_refl).
      cbn [fp_item] in Hh. exact Hh. }
    cbn [omerge map tl].
    destruct (g * p <=? bkp fee) eqn:Hgate.
    + unfold runt. cbv beta iota zeta.
      set (o := runp g g fee t (of_state st0) brd0 nrd0 0 0 0 [] zerof
                     (deb0 fee (g * p))) in *.
      assert (Hw0 : forall k : key, In k (map fst ([] : buffer)) -> In k FW)
        by (intros k0 Hk0; destruct Hk0).
      destruct (fp_sound g g fee t (of_state st0) brd0 nrd0 0 0 0 []
                  zerof (deb0 fee (g * p)) FR FW Hfp Hw0)
        as [HA [HB [HC HD]]].
      fold o in HA, HB, HC, HD.
      assert (Evs : valid stp (o_slog o) = true).
      { eapply valid_stable.
        - unfold o. apply valid_self_s.
        - intros k0 Hin. apply in_map_iff in Hin.
          destruct Hin as [[k1 v1] [Hf Hp1]]. cbn in Hf. subst k1.
          apply Hag. intro HkW.
          exact (HW 0 FR eq_refl k0 HkW (HA k0 v1 Hp1)). }
      assert (Evb : bvalid bkp (o_blog o) = true) by (rewrite HC; reflexivity).
      assert (Evn : nvalid nmp (o_nlog o) = true) by (rewrite HD; reflexivity).
      rewrite Evs, Evb, Evn. cbn [andb].
      unfold finish. cbv zeta.
      destruct (o_ok o) eqn:Hok; cbv beta iota.
      * match goal with
        | |- context [omerge ?M rest ?SPS] =>
            assert (HI : snd (omerge M rest SPS) = 0)
        end.
        { apply (IH FRs' FWs' st0 brd0 nrd0 _ _ _ (FW ++ W)); try assumption.
          - intros j i' FR' FW' E1 E2 E3.
            exact (Hcert (S j) i' FR' FW' E1 E2 E3).
          - intros j k FWj FRk Hjk E1 E2.
            apply (Hdisj (S j) (S k) FWj FRk); [lia | exact E1 | exact E2].
          - intros j FRj Ej k0 HkW HkR.
            apply in_app_or in HkW. destruct HkW as [HkFW | HkW].
            + exact (Hdisj 0 (S j) FW FRj (Nat.lt_0_succ j) eq_refl Ej
                       k0 HkFW HkR).
            + exact (HW (S j) FRj Ej k0 HkW HkR).
          - intros k0 Hnin.
            assert (HnFW : ~ In k0 (map fst (o_buf o))).
            { intro Hx. apply Hnin. apply in_or_app. left. exact (HB k0 Hx). }
            rewrite (commit_untouched (o_buf o) stp k0 HnFW).
            apply Hag. intro HxW. apply Hnin. apply in_or_app. right.
            exact HxW. }
        match goal with
        | |- context [omerge ?M rest ?SPS] =>
            destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
        end.
        cbn [snd] in HI. cbn [snd]. exact HI.
      * match goal with
        | |- context [omerge ?M rest ?SPS] =>
            assert (HI : snd (omerge M rest SPS) = 0)
        end.
        { apply (IH FRs' FWs' st0 brd0 nrd0 _ _ _ (FW ++ W)); try assumption.
          - intros j i' FR' FW' E1 E2 E3.
            exact (Hcert (S j) i' FR' FW' E1 E2 E3).
          - intros j k FWj FRk Hjk E1 E2.
            apply (Hdisj (S j) (S k) FWj FRk); [lia | exact E1 | exact E2].
          - intros j FRj Ej k0 HkW HkR.
            apply in_app_or in HkW. destruct HkW as [HkFW | HkW].
            + exact (Hdisj 0 (S j) FW FRj (Nat.lt_0_succ j) eq_refl Ej
                       k0 HkFW HkR).
            + exact (HW (S j) FRj Ej k0 HkW HkR).
          - intros k0 Hnin. apply Hag. intro HxW. apply Hnin.
            apply in_or_app. right. exact HxW. }
        match goal with
        | |- context [omerge ?M rest ?SPS] =>
            destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
        end.
        cbn [snd] in HI. cbn [snd]. exact HI.
    + match goal with
      | |- context [omerge ?M rest ?SPS] =>
          assert (HI : snd (omerge M rest SPS) = 0)
      end.
      { apply (IH FRs' FWs' st0 brd0 nrd0 _ _ _ W); try assumption.
        - intros j i' FR' FW' E1 E2 E3.
          exact (Hcert (S j) i' FR' FW' E1 E2 E3).
        - intros j k FWj FRk Hjk E1 E2.
          apply (Hdisj (S j) (S k) FWj FRk); [lia | exact E1 | exact E2].
        - intros j FRj Ej. exact (HW (S j) FRj Ej). }
      match goal with
      | |- context [omerge ?M rest ?SPS] =>
          destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
      end.
      cbn [snd] in HI. cbn [snd]. exact HI.
Qed.

(** A block whose items carry certified pairwise write-read-disjoint static
    footprints merges from base-state speculation without a single
    re-execution, and its work is exactly its non-rejected count. *)

Theorem static_disjoint_free :
  forall ts (FRs FWs : list (list key)) (st : storage) (bk : bank)
         (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    snd (omerge (st, bk, nm) ts
                (map (fun _ => spec_of (st, bk, nm)) ts)) = 0.
Proof.
  intros ts FRs FWs st bk nm HlenR HlenW Hcert Hdisj.
  apply (static_go ts FRs FWs st (of_bank bk) (of_nonces nm) st bk nm []);
    try assumption.
  - intros j FRj _ k Hk. destruct Hk.
  - intros k _. reflexivity.
Qed.

Theorem work_disjoint :
  forall ts (FRs FWs : list (list key)) (st : storage) (bk : bank)
         (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
    (forall j k FWj FRk,
        j < k ->
        nth_error FWs j = Some FWj ->
        nth_error FRs k = Some FRk -> disjoint FWj FRk) ->
    executions (st, bk, nm) ts (map (fun _ => spec_of (st, bk, nm)) ts)
    = nonrejected (snd (seq_execr (st, bk, nm) ts)).
Proof.
  intros ts FRs FWs st bk nm HlenR HlenW Hcert Hdisj.
  rewrite executions_law.
  2:{ rewrite length_map. lia. }
  rewrite (static_disjoint_free ts FRs FWs st bk nm HlenR HlenW Hcert Hdisj).
  rewrite (optimistic_correct ts (map (fun _ => spec_of (st, bk, nm)) ts)
             (st, bk, nm)).
  lia.
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
  destruct (nth j ts ditem) as [[[fee t] g] p].
  unfold step.
  destruct (g * p <=? bkq fee) eqn:Hgate.
  - unfold finish. cbv zeta.
    destruct (o_ok (runt (fee, t, g, p) (of_state stq) (of_bank bkq)
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

Lemma cbuf_keys :
  forall m ts (FRs FWs : list (list key)) j i FR FW,
    nth_error ts j = Some i ->
    nth_error FRs j = Some FR ->
    nth_error FWs j = Some FW ->
    fp_item FR FW i ->
    forall kk, In kk (map fst (cbuf m ts j)) -> In kk FW.
Proof.
  intros m ts FRs FWs j i FR FW Hi HFR HFW Hfp kk Hin.
  unfold cbuf in Hin.
  rewrite (nth_error_nth ts j ditem Hi) in Hin.
  destruct (mach_at m ts j) as [[stq bkq] nmq].
  destruct i as [[[fee t] g] p].
  cbn [fp_item] in Hfp.
  unfold step in Hin.
  destruct (g * p <=? bkq fee) eqn:Hgate.
  - unfold finish in Hin. cbv zeta in Hin.
    unfold runt in Hin. cbv beta iota zeta in Hin.
    assert (Hw0 : forall k : key, In k (map fst ([] : buffer)) -> In k FW)
      by (intros k0 Hk0; destruct Hk0).
    destruct (fp_sound g g fee t (of_state stq) (of_bank bkq) (of_nonces nmq)
                0 0 0 [] zerof (deb0 fee (g * p)) FR FW Hfp Hw0)
      as [_ [HB _]].
    destruct (o_ok (runp g g fee t (of_state stq) (of_bank bkq)
                         (of_nonces nmq) 0 0 0 [] zerof (deb0 fee (g * p))))
      eqn:Hok; cbv beta iota in Hin; cbn [fst snd] in Hin.
    + exact (HB kk Hin).
    + destruct Hin.
  - cbn [fst snd] in Hin. destruct Hin.
Qed.

(** ** Estimated dependencies and versioned speculation

    [mv_go] is the engine: block positions speculate against versioned
    storages selected by an arbitrary inclusion policy [keepf], and every
    position whose policy provably covers its write-read dependencies
    validates, so re-executions are bounded by the positions [P] does not
    certify.  Dependency estimation and the parallel-depth bound are both
    instances. *)

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

Lemma mv_go :
  forall ts (ts0 : list item) (FRs FWs : list (list key)) (m : mach)
         (brd0 : breader) (nrd0 : nreader)
         (keepf : nat -> nat -> bool) (P : nat -> bool) (d : nat),
    (forall j, nth_error ts0 (d + j) = nth_error ts j) ->
    d + length ts = length ts0 ->
    length FRs = length ts0 ->
    length FWs = length ts0 ->
    (forall j i FR FW,
        nth_error ts0 j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
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
    intros ts0 FRs FWs m brd0 nrd0 keepf P d Hsuf Hd HlenR HlenW Hcert Hsafe.
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
    destruct i0 as [[[fee t] g] p].
    assert (Hfp : fp FR FW fee t).
    { assert (Hh := Hcert d (fee, t, g, p) FR FW Hi0 HFR HFW).
      cbn [fp_item] in Hh. exact Hh. }
    destruct (mach_at m ts0 d) as [[stq bkq] nmq] eqn:EM.
    cbn [length seq map omerge tl].
    assert (HSd : fst (step (stq, bkq, nmq) (fee, t, g, p))
                  = mach_at m ts0 (S d)).
    { rewrite (mach_at_S ts0 m d Hdlen).
      rewrite (nth_error_nth ts0 d ditem Hi0).
      rewrite EM. reflexivity. }
    assert (Hcnt : length (filter (fun j => negb (P j))
                            (d :: seq (S d) (length rest)))
                   = (if negb (P d) then 1 else 0)
                     + length (filter (fun j => negb (P j))
                                (seq (S d) (length rest)))).
    { cbn [filter]. destruct (negb (P d)); cbn [length]; lia. }
    rewrite Hcnt.
    destruct (g * p <=? bkq fee) eqn:Hgate.
    + set (s' := mvstor m ts0 (keepf d) d) in *.
      unfold runt. cbv beta iota zeta.
      set (o := runp g g fee t (of_state s') brd0 nrd0 0 0 0 [] zerof
                     (deb0 fee (g * p))) in *.
      assert (Hw0 : forall k : key, In k (map fst ([] : buffer)) -> In k FW)
        by (intros k0 Hk0; destruct Hk0).
      destruct (fp_sound g g fee t (of_state s') brd0 nrd0 0 0 0 []
                  zerof (deb0 fee (g * p)) FR FW Hfp Hw0)
        as [HA [HB [HC HD]]].
      fold o in HA, HB, HC, HD.
      assert (Evb : bvalid bkq (o_blog o) = true) by (rewrite HC; reflexivity).
      assert (Evn : nvalid nmq (o_nlog o) = true) by (rewrite HD; reflexivity).
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
          assert (HFRe1 : exists FWi, nth_error FWs i1 = Some FWi).
          { destruct (nth_error FWs i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HFRe1 as [FWi HFWi].
          assert (HIe1 : exists ii, nth_error ts0 i1 = Some ii).
          { destruct (nth_error ts0 i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HIe1 as [ii Hii].
          assert (HFRe2 : exists FRi, nth_error FRs i1 = Some FRi).
          { destruct (nth_error FRs i1) eqn:E1; [eauto |].
            apply nth_error_None in E1. lia. }
          destruct HFRe2 as [FRi HFRi].
          assert (HinFWi : In kk2 FWi).
          { apply (cbuf_keys m ts0 FRs FWs i1 ii FRi FWi Hii HFRi HFWi
                     (Hcert i1 ii FRi FWi Hii HFRi HFWi) kk2 Hkk2). }
          exact (Hsafe d i1 FR FWi Hi1 Hdlen HP HFR HFWi Hki1 kk2
                   HinFWi HinK). }
        assert (Evs : valid stq (o_slog o) = true).
        { eapply valid_stable.
          - unfold o. apply valid_self_s.
          - intros kk Hin. symmetry. apply Hagree. exact Hin. }
        rewrite Evs, Evb, Evn. cbn [andb].
        assert (Ho : runp g g fee t (of_state stq) (of_bank bkq)
                          (of_nonces nmq) 0 0 0 [] zerof (deb0 fee (g * p))
                     = o).
        { unfold o. apply replay.
          - intros kk vv Hin.
            exact (valid_true_In (o_slog o) stq Evs kk vv Hin).
          - intros aa vv Hin. fold o in Hin. rewrite HC in Hin. destruct Hin.
          - intros aa vv Hin. fold o in Hin. rewrite HD in Hin. destruct Hin. }
        assert (Hstep : step (stq, bkq, nmq) (fee, t, g, p)
                        = finish stq bkq nmq fee g p o).
        { unfold step. rewrite Hgate. unfold runt. cbv beta iota zeta.
          rewrite Ho. reflexivity. }
        rewrite <- Hstep.
        destruct (step (stq, bkq, nmq) (fee, t, g, p)) as [m1 r] eqn:ES.
        assert (Hm1 : m1 = mach_at m ts0 (S d)).
        { rewrite <- HSd. reflexivity. }
        rewrite Hm1.
        match goal with
        | |- context [omerge ?M rest ?SPS] =>
            assert (HI : snd (omerge M rest SPS)
                         <= length (filter (fun j => negb (P j))
                                     (seq (S d) (length rest))))
        end.
        { apply (IH ts0 FRs FWs m brd0 nrd0 keepf P (S d)
                    Hsuf' Hd' HlenR HlenW Hcert Hsafe). }
        match goal with
        | |- context [omerge ?M rest ?SPS] =>
            destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
        end.
        cbn [snd] in HI. cbn [snd negb]. lia.
      * (* uncertified position: validated or re-executed, both advance *)
        destruct (valid stq (o_slog o) && bvalid bkq (o_blog o)
                  && nvalid nmq (o_nlog o)) eqn:Ev.
        -- apply andb_true_iff in Ev. destruct Ev as [Ev1 Evn'].
           apply andb_true_iff in Ev1. destruct Ev1 as [Evs' Evb'].
           assert (Ho : runp g g fee t (of_state stq) (of_bank bkq)
                             (of_nonces nmq) 0 0 0 [] zerof
                             (deb0 fee (g * p)) = o).
           { unfold o. apply replay.
             - intros kk vv Hin.
               exact (valid_true_In (o_slog o) stq Evs' kk vv Hin).
             - intros aa vv Hin. fold o in Hin. rewrite HC in Hin. destruct Hin.
             - intros aa vv Hin. fold o in Hin. rewrite HD in Hin. destruct Hin. }
           assert (Hstep : step (stq, bkq, nmq) (fee, t, g, p)
                           = finish stq bkq nmq fee g p o).
           { unfold step. rewrite Hgate. unfold runt. cbv beta iota zeta.
             rewrite Ho. reflexivity. }
           rewrite <- Hstep.
           destruct (step (stq, bkq, nmq) (fee, t, g, p)) as [m1 r] eqn:ES.
           assert (Hm1 : m1 = mach_at m ts0 (S d)).
           { rewrite <- HSd. reflexivity. }
           rewrite Hm1.
           match goal with
           | |- context [omerge ?M rest ?SPS] =>
               assert (HI : snd (omerge M rest SPS)
                            <= length (filter (fun j => negb (P j))
                                        (seq (S d) (length rest))))
           end.
           { apply (IH ts0 FRs FWs m brd0 nrd0 keepf P (S d)
                       Hsuf' Hd' HlenR HlenW Hcert Hsafe). }
           match goal with
           | |- context [omerge ?M rest ?SPS] =>
               destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
           end.
           cbn [snd] in HI. cbn [snd negb]. lia.
        -- destruct (step (stq, bkq, nmq) (fee, t, g, p)) as [m1 r] eqn:ES.
           assert (Hm1 : m1 = mach_at m ts0 (S d)).
           { rewrite <- HSd. reflexivity. }
           rewrite Hm1.
           match goal with
           | |- context [omerge ?M rest ?SPS] =>
               assert (HI : snd (omerge M rest SPS)
                            <= length (filter (fun j => negb (P j))
                                        (seq (S d) (length rest))))
           end.
           { apply (IH ts0 FRs FWs m brd0 nrd0 keepf P (S d)
                       Hsuf' Hd' HlenR HlenW Hcert Hsafe). }
           match goal with
           | |- context [omerge ?M rest ?SPS] =>
               destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
           end.
           cbn [snd] in HI. cbn [snd negb]. lia.
    + (* rejected: the machine does not move *)
      assert (Hm1 : (stq, bkq, nmq) = mach_at m ts0 (S d)).
      { rewrite <- HSd. unfold step. rewrite Hgate. reflexivity. }
      rewrite Hm1.
      match goal with
      | |- context [omerge ?M rest ?SPS] =>
          assert (HI : snd (omerge M rest SPS)
                       <= length (filter (fun j => negb (P j))
                                   (seq (S d) (length rest))))
      end.
      { apply (IH ts0 FRs FWs m brd0 nrd0 keepf P (S d)
                  Hsuf' Hd' HlenR HlenW Hcert Hsafe). }
      match goal with
      | |- context [omerge ?M rest ?SPS] =>
          destruct (omerge M rest SPS) as [[m2 rs] cnt] eqn:E
      end.
      cbn [snd] in HI. cbn [snd].
      destruct (negb (P d)); lia.
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
    which no position re-executes at all, against the general bound of one
    re-execution per position. *)

Theorem estimated_order_free :
  forall ts (FRs FWs : list (list key)) (E : nat -> nat -> bool)
         (ord : list nat) (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
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
  intros ts FRs FWs E ord st bk nm HlenR HlenW Hcert HE Hresp.
  assert (Hle := mv_go ts ts FRs FWs (st, bk, nm) (of_bank bk) (of_nonces nm)
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
  cbn [mach_at] in Hle.
  lia.
Qed.

(** Parallel depth: any height function [L] that strictly increases along
    forward write-read dependencies bounds the rounds of versioned
    speculation.  Round [r] keeps every position of height at most [r];
    every position of height at most [S r] then validates, so
    re-executions are bounded by the positions above [S r], and rounds
    up to the critical path converge to none. *)

Theorem level_rounds_bound :
  forall ts (FRs FWs : list (list key)) (L : nat -> nat) (r : nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
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
  intros ts FRs FWs L r st bk nm HlenR HlenW Hcert HL.
  assert (Hle := mv_go ts ts FRs FWs (st, bk, nm) (of_bank bk) (of_nonces nm)
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
  forall ts (FRs FWs : list (list key)) (L : nat -> nat) (r : nat)
         (st : storage) (bk : bank) (nm : nonces),
    length FRs = length ts ->
    length FWs = length ts ->
    (forall j i FR FW,
        nth_error ts j = Some i ->
        nth_error FRs j = Some FR ->
        nth_error FWs j = Some FW -> fp_item FR FW i) ->
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
  intros ts FRs FWs L r st bk nm HlenR HlenW Hcert HL Hmax.
  assert (Hle := level_rounds_bound ts FRs FWs L r st bk nm
                   HlenR HlenW Hcert HL).
  rewrite (filter_false_in nat (fun j => negb (L j <=? S r))) in Hle.
  2:{ intros x Hx. apply in_seq in Hx.
      assert (Hlx : L x <= S r) by (apply Hmax; lia).
      apply Nat.leb_le in Hlx. rewrite Hlx. reflexivity. }
  cbn [length] in Hle.
  lia.
Qed.

(** ** The operational concurrent scheduler

    Workers over a multi-version store under an explicit interleaving
    semantics.  A state carries the committed prefix length, the committed
    machine, the committed receipts, and the speculative outcomes of
    executed but uncommitted positions.  [AExec j] runs position [j]
    against the versioned store of the moment: committed storage overlaid,
    in index order, with the write buffers of executed lower positions;
    any interleaving of executions is allowed, and re-execution simply
    overwrites.  [ACommit] drives the commit wavefront: it validates the
    head position's speculation against the committed machine, commits it
    unchanged on agreement, re-executes it against the true prefix on
    disagreement or absence, and rejects an unfunded transaction without
    running it. *)

Record ostate : Type := OSt {
  os_c  : nat;
  os_m  : mach;
  os_rs : list rcpt;
  os_ex : nat -> option out
}.

Definition obuf (s : ostate) (i : nat) : buffer :=
  match os_ex s i with
  | Some o => if o_ok o then o_buf o else []
  | None => []
  end.

Fixpoint ostor_go (base : storage) (ob : nat -> buffer)
                  (from cnt : nat) : storage :=
  match cnt with
  | 0 => base
  | S c => ostor_go (commit base (ob from)) ob (S from) c
  end.

Definition oread (s : ostate) (j : nat) : reader :=
  fun _ kk =>
    ostor_go (fst (fst (os_m s))) (obuf s) (os_c s) (j - os_c s) kk.

Inductive oact : Type :=
| AExec (j : nat)
| ACommit.

Definition ostep (ts : list item) (s : ostate) (a : oact) : ostate :=
  match a with
  | AExec j =>
      if (os_c s <=? j) && (j <? length ts)
      then match nth_error ts j with
           | Some i =>
               OSt (os_c s) (os_m s) (os_rs s)
                   (fun j' => if j' =? j
                              then Some (runt i (oread s j)
                                           (of_bank (snd (fst (os_m s))))
                                           (of_nonces (snd (os_m s))))
                              else os_ex s j')
           | None => s
           end
      else s
  | ACommit =>
      if os_c s <? length ts
      then match nth_error ts (os_c s) with
           | Some i =>
               let '(st, bk, nm) := os_m s in
               let '(fee, t, g, p) := i in
               if g * p <=? bk fee
               then
                 match os_ex s (os_c s) with
                 | Some o =>
                     if valid st (o_slog o) && bvalid bk (o_blog o)
                        && nvalid nm (o_nlog o)
                     then let '(m1, r) := finish st bk nm fee g p o in
                          OSt (S (os_c s)) m1 (os_rs s ++ [r]) (os_ex s)
                     else let '(m1, r) := step (st, bk, nm) (fee, t, g, p) in
                          OSt (S (os_c s)) m1 (os_rs s ++ [r]) (os_ex s)
                 | None =>
                     let '(m1, r) := step (st, bk, nm) (fee, t, g, p) in
                     OSt (S (os_c s)) m1 (os_rs s ++ [r]) (os_ex s)
                 end
               else OSt (S (os_c s)) (st, bk, nm)
                        (os_rs s ++ [(SRejected, 0, [], [], [])]) (os_ex s)
           | None => s
           end
      else s
  end.

Definition oinit (m0 : mach) : ostate := OSt 0 m0 [] (fun _ => None).

Definition reach (ts : list item) (s0 : ostate) (acts : list oact) : ostate :=
  fold_left (ostep ts) acts s0.

Lemma seq_rcpt_len :
  forall ts m, length (snd (seq_execr m ts)) = length ts.
Proof.
  induction ts as [| i rest IH]; intros m; cbn [seq_execr].
  - reflexivity.
  - destruct (step m i) as [m1 r].
    destruct (seq_execr m1 rest) as [m2 rs] eqn:E.
    assert (HI := IH m1). rewrite E in HI. cbn in HI |- *. lia.
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

Definition oinv (m0 : mach) (ts : list item) (s : ostate) : Prop :=
  os_c s <= length ts
  /\ os_m s = mach_at m0 ts (os_c s)
  /\ os_rs s = firstn (os_c s) (snd (seq_execr m0 ts))
  /\ (forall j o, os_ex s j = Some o ->
        exists rd brd nrd i,
          nth_error ts j = Some i /\ o = runt i rd brd nrd).

Lemma ostep_inv :
  forall ts m0 s a,
    oinv m0 ts s -> oinv m0 ts (ostep ts s a).
Proof.
  intros ts m0 s a [Hc [Hm [Hr He]]].
  destruct a as [j |].
  - (* AExec: commit data untouched, one slot refreshed *)
    cbn [ostep].
    destruct ((os_c s <=? j) && (j <? length ts));
      [| exact (conj Hc (conj Hm (conj Hr He)))].
    destruct (nth_error ts j) as [i |] eqn:Hij;
      [| exact (conj Hc (conj Hm (conj Hr He)))].
    cbn [os_c os_m os_rs os_ex].
    split; [exact Hc |]. split; [exact Hm |]. split; [exact Hr |].
    intros j0 o Ho.
    cbn beta in Ho.
    destruct (j0 =? j) eqn:Hjj.
    + apply Nat.eqb_eq in Hjj. subst j0.
      cbn in Ho. rewrite Nat.eqb_refl in Ho. cbn in Ho.
      injection Ho as <-.
      exists (oread s j), (of_bank (snd (fst (os_m s)))),
             (of_nonces (snd (os_m s))), i.
      split; [exact Hij | reflexivity].
    + cbn in Ho. rewrite Hjj in Ho. cbn in Ho.
      exact (He j0 o Ho).
  - cbn [ostep].
    destruct (os_c s <? length ts) eqn:Hlt;
      [| exact (conj Hc (conj Hm (conj Hr He)))].
    apply Nat.ltb_lt in Hlt.
    destruct (nth_error ts (os_c s)) as [i |] eqn:Hi;
      [| exfalso; apply nth_error_None in Hi; lia].
    assert (Hnth : nth (os_c s) ts ditem = i)
      by (apply nth_error_nth; exact Hi).
    assert (Hrs' : forall r,
               r = snd (step (mach_at m0 ts (os_c s)) i) ->
               os_rs s ++ [r]
               = firstn (S (os_c s)) (snd (seq_execr m0 ts))).
    { intros r Hrr.
      rewrite (firstn_succ_nth rcpt (snd (seq_execr m0 ts)) (os_c s)
                 (SRejected, 0, [], [], [])).
      2:{ rewrite seq_rcpt_len. exact Hlt. }
      rewrite Hr. f_equal. f_equal.
      assert (Hn := seq_rcpt_nth ts m0 (os_c s) Hlt).
      rewrite Hnth in Hn.
      apply (nth_error_nth (snd (seq_execr m0 ts)) (os_c s)
               (SRejected, 0, [], [], [])) in Hn.
      rewrite Hn. rewrite Hrr. reflexivity. }
    assert (Hma : forall m1,
               m1 = fst (step (mach_at m0 ts (os_c s)) i) ->
               m1 = mach_at m0 ts (S (os_c s))).
    { intros m1 Hm1.
      rewrite (mach_at_S ts m0 (os_c s) Hlt). rewrite Hnth. exact Hm1. }
    destruct (os_m s) as [[st bk] nm] eqn:EOM.
    destruct i as [[[fee t] g] p].
    cbv beta iota.
    destruct (g * p <=? bk fee) eqn:Hgate.
    + assert (Hstq : mach_at m0 ts (os_c s) = (st, bk, nm))
        by (symmetry; exact Hm).
      destruct (os_ex s (os_c s)) as [o |] eqn:Hex.
      * destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                  && nvalid nm (o_nlog o)) eqn:Ev.
        -- apply andb_true_iff in Ev. destruct Ev as [Ev1 Evn].
           apply andb_true_iff in Ev1. destruct Ev1 as [Evs Evb].
           destruct (He (os_c s) o Hex)
             as [rd0 [brd0 [nrd0 [i' [Hi' Ho']]]]].
           rewrite Hi in Hi'. injection Hi' as Hii. subst i'. subst o.
           assert (Ho : runt (fee, t, g, p) (of_state st) (of_bank bk)
                             (of_nonces nm)
                        = runt (fee, t, g, p) rd0 brd0 nrd0).
           { apply replay_runt; assumption. }
           assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                           = finish st bk nm fee g p
                               (runt (fee, t, g, p) rd0 brd0 nrd0)).
           { unfold step. rewrite Hgate. rewrite Ho. reflexivity. }
           destruct (finish st bk nm fee g p
                       (runt (fee, t, g, p) rd0 brd0 nrd0)) as [m1 r] eqn:EF.
           cbn [os_c os_m os_rs os_ex].
           split; [cbn; lia |].
           split; [| split].
           ++ apply Hma. rewrite Hstq. rewrite Hstep. reflexivity.
           ++ apply Hrs'. rewrite Hstq. rewrite Hstep. reflexivity.
           ++ exact He.
        -- destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r] eqn:ES.
           cbn [os_c os_m os_rs os_ex].
           split; [cbn; lia |].
           split; [| split].
           ++ apply Hma. rewrite Hstq. rewrite ES. reflexivity.
           ++ apply Hrs'. rewrite Hstq. rewrite ES. reflexivity.
           ++ exact He.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r] eqn:ES.
        cbn [os_c os_m os_rs os_ex].
        split; [cbn; lia |].
        split; [| split].
        -- apply Hma. rewrite Hstq. rewrite ES. reflexivity.
        -- apply Hrs'. rewrite Hstq. rewrite ES. reflexivity.
        -- exact He.
    + assert (Hstq : mach_at m0 ts (os_c s) = (st, bk, nm))
        by (symmetry; exact Hm).
      assert (ES : step (st, bk, nm) (fee, t, g, p)
                   = ((st, bk, nm), (SRejected, 0, [], [], []))).
      { unfold step. rewrite Hgate. reflexivity. }
      cbn [os_c os_m os_rs os_ex].
      split; [cbn; lia |].
      split; [| split].
      * apply Hma. rewrite Hstq. rewrite ES. reflexivity.
      * apply Hrs'. rewrite Hstq. rewrite ES. reflexivity.
      * exact He.
Qed.

Lemma reach_inv :
  forall ts m0 acts s,
    oinv m0 ts s -> oinv m0 ts (fold_left (ostep ts) acts s).
Proof.
  intros ts m0 acts. induction acts as [| a acts' IH]; intros s Hs; cbn.
  - exact Hs.
  - apply IH. apply ostep_inv. exact Hs.
Qed.

(** Safety: however executions interleave, once the wavefront has crossed
    the block the committed machine and receipts are sequential
    execution's. *)

Theorem op_safety :
  forall ts m0 acts,
    os_c (reach ts (oinit m0) acts) = length ts ->
    os_m (reach ts (oinit m0) acts) = fst (seq_execr m0 ts)
    /\ os_rs (reach ts (oinit m0) acts) = snd (seq_execr m0 ts).
Proof.
  intros ts m0 acts Hdone.
  assert (H0 : oinv m0 ts (oinit m0)).
  { split; [cbn; lia |]. split; [reflexivity |]. split; [reflexivity |].
    intros j o Hno. discriminate. }
  assert (Hs := reach_inv ts m0 acts (oinit m0) H0).
  destruct Hs as [Hc [Hm [Hr He]]].
  unfold reach in *.
  rewrite Hdone in Hm, Hr.
  split.
  - rewrite Hm. apply mach_at_full.
  - rewrite Hr. apply firstn_all2. rewrite seq_rcpt_len. lia.
Qed.

(** Liveness: a commit action always advances the wavefront, an execution
    never retards it, so any schedule containing at least as many commit
    actions as the block is long finishes the block, whatever else it
    interleaves and in whatever order. *)

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
  destruct i as [[[fee t] g] p].
  cbv beta iota.
  destruct (g * p <=? bk fee).
  - destruct (os_ex s (os_c s)) as [o |].
    + destruct (valid st (o_slog o) && bvalid bk (o_blog o)
                && nvalid nm (o_nlog o)).
      * destruct (finish st bk nm fee g p o) as [m1 r]. reflexivity.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r]. reflexivity.
    + destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r]. reflexivity.
  - reflexivity.
Qed.

Lemma exec_keeps :
  forall ts s j, os_c (ostep ts s (AExec j)) = os_c s.
Proof.
  intros ts s j. cbn [ostep].
  destruct ((os_c s <=? j) && (j <? length ts)); [| reflexivity].
  destruct (nth_error ts j) as [i |]; reflexivity.
Qed.

Definition is_commit (a : oact) : bool :=
  match a with ACommit => true | _ => false end.

Lemma osc_lower :
  forall ts acts s,
    Nat.min (length ts)
            (os_c s + length (filter is_commit acts))
    <= os_c (fold_left (ostep ts) acts s).
Proof.
  intros ts acts. induction acts as [| a acts' IH]; intros s; cbn [fold_left].
  - cbn [filter length]. lia.
  - destruct a as [j |].
    + cbn [filter is_commit].
      etransitivity; [| apply IH].
      rewrite exec_keeps. lia.
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
  assert (Hlow := osc_lower ts acts (oinit m0)).
  assert (H0 : oinv m0 ts (oinit m0)).
  { split; [cbn; lia |]. split; [reflexivity |]. split; [reflexivity |].
    intros j o Hno. discriminate. }
  assert (Hup := reach_inv ts m0 acts (oinit m0) H0).
  destruct Hup as [Hc _].
  unfold reach. cbn [os_c oinit] in *.
  lia.
Qed.

(** ** Finite-map machines and the executable engine

    Storage, bank, and nonces refine to association maps; the engine runs
    the same executor against readers built from map lookups and performs
    its updates on the maps.  Simulation is pointwise machine agreement
    plus receipt equality, carried through replay: pointwise-equal read
    sources reproduce a run's logs, so both sides make identical
    decisions. *)

Definition fmap (K : Type) : Type := list (K * nat).

Fixpoint flook {K : Type} (kb : K -> K -> bool) (m : fmap K) (k : K) : nat :=
  match m with
  | [] => 0
  | (k', v) :: r => if kb k k' then v else flook kb r k
  end.

Fixpoint fupd {K : Type} (kb : K -> K -> bool) (m : fmap K) (k : K) (v : nat)
  : fmap K :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: r => if kb k k' then (k, v) :: r else (k', v') :: fupd kb r k v
  end.

Lemma flook_fupd :
  forall (K : Type) (kb : K -> K -> bool)
         (kb_spec : forall x y, kb x y = true <-> x = y)
         (m : fmap K) (k k' : K) (v : nat),
    flook kb (fupd kb m k v) k' = if kb k' k then v else flook kb m k'.
Proof.
  intros K kb kb_spec m k k' v.
  induction m as [| [k0 v0] r IH]; cbn.
  - destruct (kb k' k) eqn:E; reflexivity.
  - destruct (kb k k0) eqn:E0; cbn.
    + destruct (kb k' k) eqn:E1.
      * reflexivity.
      * apply kb_spec in E0. subst k0.
        rewrite E1. reflexivity.
    + destruct (kb k' k0) eqn:E1.
      * apply kb_spec in E1. subst k0.
        destruct (kb k' k) eqn:E2.
        -- apply kb_spec in E2. subst k'.
           rewrite (proj2 (kb_spec k k) eq_refl) in E0. discriminate.
        -- reflexivity.
      * exact IH.
Qed.

Lemma keqb_spec : forall x y : key, keqb x y = true <-> x = y.
Proof. exact keqb_eq. Qed.

Lemma neqb_spec : forall x y : nat, (x =? y) = true <-> x = y.
Proof. intros x y. apply Nat.eqb_eq. Qed.

Definition machF : Type := (fmap key * fmap addr * fmap addr)%type.

Definition stF (mf : machF) : fmap key := fst (fst mf).
Definition bkF (mf : machF) : fmap addr := snd (fst mf).
Definition nmF (mf : machF) : fmap addr := snd mf.

Definition mEq (mf : machF) (m : mach) : Prop :=
  (forall kk, flook keqb (stF mf) kk = fst (fst m) kk)
  /\ (forall a, flook Nat.eqb (bkF mf) a = snd (fst m) a)
  /\ (forall a, flook Nat.eqb (nmF mf) a = snd m a).

Definition commitF (stf : fmap key) (w : buffer) : fmap key :=
  fold_right (fun p sf => fupd keqb sf (fst p) (snd p)) stf w.

Lemma commitF_sim :
  forall w stf (s : storage),
    (forall kk, flook keqb stf kk = s kk) ->
    forall kk, flook keqb (commitF stf w) kk = commit s w kk.
Proof.
  induction w as [| [k0 v0] w' IH]; cbn; intros stf s Hpt kk.
  - apply Hpt.
  - rewrite (flook_fupd key keqb keqb_spec).
    unfold kupd.
    destruct (keqb kk k0); [reflexivity | apply IH; exact Hpt].
Qed.

Fixpoint apply_tvsF (bf : fmap addr) (l : list transfer) : fmap addr :=
  match l with
  | [] => bf
  | (s, d, amt) :: r =>
      let bf1 := fupd Nat.eqb bf s (flook Nat.eqb bf s - amt) in
      apply_tvsF (fupd Nat.eqb bf1 d (flook Nat.eqb bf1 d + amt)) r
  end.

Lemma apply_tvsF_sim :
  forall l bf (b : bank),
    (forall a, flook Nat.eqb bf a = b a) ->
    forall a, flook Nat.eqb (apply_tvsF bf l) a = apply_tvs b l a.
Proof.
  induction l as [| [[s d] amt] r IH]; cbn; intros bf b Hpt a.
  - apply Hpt.
  - apply IH.
    intros a0.
    rewrite !(flook_fupd nat Nat.eqb neqb_spec).
    unfold bupd.
    rewrite !Hpt.
    destruct (a0 =? d); destruct (a0 =? s); destruct (d =? s); reflexivity.
Qed.

Definition finishF (stf : fmap key) (bkf nmf : fmap addr)
                   (fee : addr) (g p : nat) (o : out) : machF * rcpt :=
  let u := g - o_gas o in
  if o_ok o
  then
    let u_eff := u - Nat.min (o_ref o) (u / 2) in
    let b1 := fupd Nat.eqb bkf fee (flook Nat.eqb bkf fee - g * p) in
    let b2 := apply_tvsF b1 (o_tvs o) in
    let b3 := fupd Nat.eqb b2 fee (flook Nat.eqb b2 fee + (g - u_eff) * p) in
    let b4 := fupd Nat.eqb b3 CB (flook Nat.eqb b3 CB + u_eff * p) in
    ((commitF stf (o_buf o), b4,
      fupd Nat.eqb nmf fee (S (flook Nat.eqb nmf fee))),
     (SOk, u_eff, o_buf o, o_evs o, o_tvs o))
  else
    ((stf,
      fupd Nat.eqb (fupd Nat.eqb bkf fee (flook Nat.eqb bkf fee - u * p)) CB
           (flook Nat.eqb (fupd Nat.eqb bkf fee
                             (flook Nat.eqb bkf fee - u * p)) CB + u * p),
      fupd Nat.eqb nmf fee (S (flook Nat.eqb nmf fee))),
     (SRev, u, [], [], [])).

Definition stepF (mf : machF) (i : item) : machF * rcpt :=
  let '(stf, bkf, nmf) := mf in
  let '(fee, t, g, p) := i in
  if g * p <=? flook Nat.eqb bkf fee
  then finishF stf bkf nmf fee g p
         (runt i (fun _ kk => flook keqb stf kk)
                 (fun _ a => flook Nat.eqb bkf a)
                 (fun _ a => flook Nat.eqb nmf a))
  else (mf, (SRejected, 0, [], [], [])).

Fixpoint seq_execrF (mf : machF) (ts : list item) : machF * list rcpt :=
  match ts with
  | [] => (mf, [])
  | i :: rest =>
      let '(mf1, r) := stepF mf i in
      let '(mf2, rs) := seq_execrF mf1 rest in
      (mf2, r :: rs)
  end.

Lemma finishF_sim :
  forall stf bkf nmf (st : storage) (bk : bank) (nm : nonces) fee g p o,
    (forall kk, flook keqb stf kk = st kk) ->
    (forall a, flook Nat.eqb bkf a = bk a) ->
    (forall a, flook Nat.eqb nmf a = nm a) ->
    mEq (fst (finishF stf bkf nmf fee g p o))
        (fst (finish st bk nm fee g p o))
    /\ snd (finishF stf bkf nmf fee g p o) = snd (finish st bk nm fee g p o).
Proof.
  intros stf bkf nmf st bk nm fee g p o Hst Hbk Hnm.
  unfold finishF, finish. cbv zeta.
  assert (Hb1 : forall a0,
             flook Nat.eqb (fupd Nat.eqb bkf fee
                              (flook Nat.eqb bkf fee - g * p)) a0
             = bupd bk fee (bk fee - g * p) a0).
  { intros a0.
    rewrite (flook_fupd nat Nat.eqb neqb_spec).
    unfold bupd. rewrite Hbk.
    destruct (a0 =? fee); rewrite ?Hbk; reflexivity. }
  assert (Hb2 : forall a0,
             flook Nat.eqb (apply_tvsF (fupd Nat.eqb bkf fee
                              (flook Nat.eqb bkf fee - g * p)) (o_tvs o)) a0
             = apply_tvs (bupd bk fee (bk fee - g * p)) (o_tvs o) a0).
  { intros a0. apply apply_tvsF_sim. exact Hb1. }
  destruct (o_ok o); cbn [fst snd].
  - split; [| reflexivity].
    split; [| split]; cbn [stF bkF nmF fst snd].
    + intros kk. apply commitF_sim. exact Hst.
    + intros a.
      rewrite !(flook_fupd nat Nat.eqb neqb_spec).
      unfold bupd.
      rewrite !Hb2.
      destruct (a =? CB); destruct (a =? fee); destruct (CB =? fee);
        rewrite ?Hb2; reflexivity.
    + intros a.
      rewrite (flook_fupd nat Nat.eqb neqb_spec).
      unfold bupd. rewrite Hnm.
      destruct (a =? fee); rewrite ?Hnm; reflexivity.
  - split; [| reflexivity].
    split; [| split]; cbn [stF bkF nmF fst snd].
    + exact Hst.
    + intros a.
      rewrite !(flook_fupd nat Nat.eqb neqb_spec).
      unfold bupd.
      rewrite !Hbk.
      destruct (a =? CB); destruct (a =? fee); destruct (CB =? fee);
        rewrite ?Hbk; reflexivity.
    + intros a.
      rewrite (flook_fupd nat Nat.eqb neqb_spec).
      unfold bupd. rewrite Hnm.
      destruct (a =? fee); rewrite ?Hnm; reflexivity.
Qed.

Lemma stepF_sim :
  forall mf m i,
    mEq mf m ->
    mEq (fst (stepF mf i)) (fst (step m i))
    /\ snd (stepF mf i) = snd (step m i).
Proof.
  intros mf m i [Hst [Hbk Hnm]].
  destruct mf as [[stf bkf] nmf]. destruct m as [[st bk] nm].
  destruct i as [[[fee t] g] p].
  cbn [stF bkF nmF fst snd] in Hst, Hbk, Hnm.
  unfold stepF, step.
  rewrite Hbk.
  destruct (g * p <=? bk fee) eqn:Hgate.
  - assert (Ho : runt (fee, t, g, p)
                   (fun _ kk => flook keqb stf kk)
                   (fun _ a => flook Nat.eqb bkf a)
                   (fun _ a => flook Nat.eqb nmf a)
                 = runt (fee, t, g, p) (of_state st) (of_bank bk)
                       (of_nonces nm)).
    { symmetry.
      unfold runt. cbv beta iota zeta.
      apply replay.
      - intros kk vv Hin.
        assert (Hv := valid_true_In _ _
                        (valid_self_s g g fee t
                           (fun kk0 => flook keqb stf kk0)
                           (fun _ a => flook Nat.eqb bkf a)
                           (fun _ a => flook Nat.eqb nmf a)
                           0 0 0 [] zerof (deb0 fee (g * p)))
                        kk vv).
        rewrite <- (Hst kk). apply Hv.
        exact Hin.
      - intros aa vv Hin.
        assert (Hv := bvalid_true_In _ _
                        (bvalid_self_b g g fee t
                           (fun _ kk0 => flook keqb stf kk0)
                           (fun a0 => flook Nat.eqb bkf a0)
                           (fun _ a0 => flook Nat.eqb nmf a0)
                           0 0 0 [] zerof (deb0 fee (g * p)))
                        aa vv).
        rewrite <- (Hbk aa). apply Hv.
        exact Hin.
      - intros aa vv Hin.
        assert (Hv := bvalid_true_In _ _
                        (nvalid_self_n g g fee t
                           (fun _ kk0 => flook keqb stf kk0)
                           (fun _ a0 => flook Nat.eqb bkf a0)
                           (fun a0 => flook Nat.eqb nmf a0)
                           0 0 0 [] zerof (deb0 fee (g * p)))
                        aa vv).
        rewrite <- (Hnm aa). apply Hv.
        exact Hin. }
    rewrite Ho.
    apply finishF_sim; assumption.
  - split; [| reflexivity].
    split; [| split]; cbn [stF bkF nmF fst snd]; assumption.
Qed.

Theorem engine_seq_correct :
  forall ts mf m,
    mEq mf m ->
    mEq (fst (seq_execrF mf ts)) (fst (seq_execr m ts))
    /\ snd (seq_execrF mf ts) = snd (seq_execr m ts).
Proof.
  induction ts as [| i rest IH]; intros mf m Hm.
  - cbn. split; [exact Hm | reflexivity].
  - cbn [seq_execrF seq_execr].
    destruct (stepF_sim mf m i Hm) as [Hm1 Hr1].
    destruct (stepF mf i) as [mf1 r1] eqn:EF.
    destruct (step m i) as [m1 r1'] eqn:ES.
    cbn [fst snd] in Hm1, Hr1. subst r1'.
    destruct (IH mf1 m1 Hm1) as [Hm2 Hr2].
    destruct (seq_execrF mf1 rest) as [mf2 rs] eqn:E2.
    destruct (seq_execr m1 rest) as [m2 rs'] eqn:E3.
    cbn [fst snd] in Hm2, Hr2. subst rs'.
    split; [exact Hm2 | reflexivity].
Qed.

Fixpoint validF (stf : fmap key) (log : list (key * val)) : bool :=
  match log with
  | [] => true
  | (k, v) :: rest => (flook keqb stf k =? v) && validF stf rest
  end.

Fixpoint bvalidF (bf : fmap addr) (log : list (addr * nat)) : bool :=
  match log with
  | [] => true
  | (a, v) :: rest => (flook Nat.eqb bf a =? v) && bvalidF bf rest
  end.

Lemma validF_sim :
  forall log stf (s : storage),
    (forall kk, flook keqb stf kk = s kk) ->
    validF stf log = valid s log.
Proof.
  induction log as [| [k v] r IH]; cbn; intros stf s Hpt.
  - reflexivity.
  - rewrite Hpt. rewrite (IH stf s Hpt). reflexivity.
Qed.

Lemma bvalidF_sim :
  forall log bf (b : bank),
    (forall a, flook Nat.eqb bf a = b a) ->
    bvalidF bf log = bvalid b log.
Proof.
  induction log as [| [a v] r IH]; cbn; intros bf b Hpt.
  - reflexivity.
  - rewrite Hpt. rewrite (IH bf b Hpt). reflexivity.
Qed.

Fixpoint omergeF (mf : machF) (ts : list item) (specs : list spec)
  : machF * list rcpt * nat :=
  match ts with
  | [] => (mf, [], 0)
  | i :: rest =>
      let '(stf, bkf, nmf) := mf in
      let '(fee, t, g, p) := i in
      if g * p <=? flook Nat.eqb bkf fee
      then
        match specs with
        | (rd, brd, nrd) :: sps =>
            let o := runt i rd brd nrd in
            if validF stf (o_slog o) && bvalidF bkf (o_blog o)
               && bvalidF nmf (o_nlog o)
            then
              let '(mf1, r) := finishF stf bkf nmf fee g p o in
              let '(mf2, rs, cnt) := omergeF mf1 rest sps in
              (mf2, r :: rs, cnt)
            else
              let '(mf1, r) := stepF mf i in
              let '(mf2, rs, cnt) := omergeF mf1 rest sps in
              (mf2, r :: rs, S cnt)
        | [] =>
            let '(mf1, r) := stepF mf i in
            let '(mf2, rs, cnt) := omergeF mf1 rest [] in
            (mf2, r :: rs, S cnt)
        end
      else
        let '(mf2, rs, cnt) := omergeF mf rest (tl specs) in
        (mf2, (SRejected, 0, [], [], []) :: rs, cnt)
  end.

Theorem engine_merge_correct :
  forall ts specs mf m,
    mEq mf m ->
    mEq (fst (fst (omergeF mf ts specs))) (fst (fst (omerge m ts specs)))
    /\ snd (fst (omergeF mf ts specs)) = snd (fst (omerge m ts specs))
    /\ snd (omergeF mf ts specs) = snd (omerge m ts specs).
Proof.
  induction ts as [| i rest IH]; intros specs mf m Hm.
  - cbn. split; [exact Hm | split; reflexivity].
  - destruct mf as [[stf bkf] nmf]. destruct m as [[st bk] nm].
    assert (Hm' := Hm).
    destruct Hm as [Hst [Hbk Hnm]].
    cbn [stF bkF nmF fst snd] in Hst, Hbk, Hnm.
    destruct i as [[[fee t] g] p].
    destruct specs as [| [[rd brd] nrd] sps]; cbn [omergeF omerge tl];
      unfold nvalid.
    + rewrite Hbk.
      destruct (g * p <=? bk fee) eqn:Hgate.
      * destruct (stepF_sim (stf, bkf, nmf) (st, bk, nm) (fee, t, g, p) Hm')
          as [Hm1 Hr1].
        destruct (stepF (stf, bkf, nmf) (fee, t, g, p)) as [mf1 r1].
        destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r1'].
        cbn [fst snd] in Hm1, Hr1. subst r1'.
        destruct (IH [] mf1 m1 Hm1) as [HA [HB HC]].
        destruct (omergeF mf1 rest []) as [[mf2 rs] cnt].
        destruct (omerge m1 rest []) as [[m2 rs'] cnt'].
        cbn [fst snd] in HA, HB, HC. subst rs' cnt'.
        split; [exact HA | split; reflexivity].
      * destruct (IH [] (stf, bkf, nmf) (st, bk, nm) Hm') as [HA [HB HC]].
        destruct (omergeF (stf, bkf, nmf) rest []) as [[mf2 rs] cnt].
        destruct (omerge (st, bk, nm) rest []) as [[m2 rs'] cnt'].
        cbn [fst snd] in HA, HB, HC. subst rs' cnt'.
        split; [exact HA | split; reflexivity].
    + rewrite Hbk.
      destruct (g * p <=? bk fee) eqn:Hgate.
      * rewrite (validF_sim _ _ st Hst).
        rewrite (bvalidF_sim _ _ bk Hbk).
        rewrite (bvalidF_sim _ _ nm Hnm).
        destruct (valid st (o_slog (runt (fee, t, g, p) rd brd nrd)) &&
                  bvalid bk (o_blog (runt (fee, t, g, p) rd brd nrd)) &&
                  bvalid nm (o_nlog (runt (fee, t, g, p) rd brd nrd)))
          eqn:Ev.
        -- destruct (finishF_sim stf bkf nmf st bk nm fee g p
                       (runt (fee, t, g, p) rd brd nrd) Hst Hbk Hnm)
             as [Hm1 Hr1].
           destruct (finishF stf bkf nmf fee g p
                       (runt (fee, t, g, p) rd brd nrd)) as [mf1 r1].
           destruct (finish st bk nm fee g p
                       (runt (fee, t, g, p) rd brd nrd)) as [m1 r1'].
           cbn [fst snd] in Hm1, Hr1. subst r1'.
           destruct (IH sps mf1 m1 Hm1) as [HA [HB HC]].
           destruct (omergeF mf1 rest sps) as [[mf2 rs] cnt].
           destruct (omerge m1 rest sps) as [[m2 rs'] cnt'].
           cbn [fst snd] in HA, HB, HC. subst rs' cnt'.
           split; [exact HA | split; reflexivity].
        -- destruct (stepF_sim (stf, bkf, nmf) (st, bk, nm) (fee, t, g, p) Hm')
             as [Hm1 Hr1].
           destruct (stepF (stf, bkf, nmf) (fee, t, g, p)) as [mf1 r1].
           destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r1'].
           cbn [fst snd] in Hm1, Hr1. subst r1'.
           destruct (IH sps mf1 m1 Hm1) as [HA [HB HC]].
           destruct (omergeF mf1 rest sps) as [[mf2 rs] cnt].
           destruct (omerge m1 rest sps) as [[m2 rs'] cnt'].
           cbn [fst snd] in HA, HB, HC. subst rs' cnt'.
           split; [exact HA | split; reflexivity].
      * destruct (IH sps (stf, bkf, nmf) (st, bk, nm) Hm') as [HA [HB HC]].
        destruct (omergeF (stf, bkf, nmf) rest sps) as [[mf2 rs] cnt].
        destruct (omerge (st, bk, nm) rest sps) as [[m2 rs'] cnt'].
        cbn [fst snd] in HA, HB, HC. subst rs' cnt'.
        split; [exact HA | split; reflexivity].
Qed.

(** ** Global supply conservation

    The bank's total supply over its finite support is invariant under
    execution: gas moves value to the coinbase and transfers move it
    between accounts, so the sum never changes, with no hypotheses on the
    map. *)

Definition bsum (bf : fmap addr) : nat :=
  fold_right (fun p acc => snd p + acc) 0 bf.

Lemma bsum_fupd :
  forall bf a v,
    bsum (fupd Nat.eqb bf a v) + flook Nat.eqb bf a = bsum bf + v.
Proof.
  induction bf as [| [a0 v0] r IH]; cbn; intros a v.
  - lia.
  - destruct (a =? a0) eqn:E; cbn.
    + lia.
    + assert (HI := IH a v). unfold bsum in HI. lia.
Qed.

Lemma apply_ok_ext :
  forall l (b b' : bank),
    (forall a, b a = b' a) ->
    apply_ok b l = apply_ok b' l.
Proof.
  induction l as [| [[s d] amt] r IH]; cbn; intros b b' Hpt.
  - reflexivity.
  - assert (Hh : b s = b' s) by apply Hpt. rewrite Hh.
    destruct (amt <=? b' s); cbn; [| reflexivity].
    apply IH. intros a. unfold bupd.
    destruct (a =? d); destruct (a =? s); destruct (d =? s);
      rewrite ?Hpt, ?Hh; reflexivity.
Qed.

Lemma bsum_apply_tvsF :
  forall l bf,
    apply_ok (fun a => flook Nat.eqb bf a) l = true ->
    bsum (apply_tvsF bf l) = bsum bf.
Proof.
  induction l as [| [[s d] amt] r IH]; cbn; intros bf Hok.
  - reflexivity.
  - apply andb_true_iff in Hok. destruct Hok as [Hle Hok].
    apply Nat.leb_le in Hle.
    set (bf1 := fupd Nat.eqb bf s (flook Nat.eqb bf s - amt)) in *.
    set (bf2 := fupd Nat.eqb bf1 d (flook Nat.eqb bf1 d + amt)) in *.
    assert (Hs1 : bsum bf1 + flook Nat.eqb bf s
                  = bsum bf + (flook Nat.eqb bf s - amt))
      by (apply bsum_fupd).
    assert (Hs2 : bsum bf2 + flook Nat.eqb bf1 d
                  = bsum bf1 + (flook Nat.eqb bf1 d + amt))
      by (apply bsum_fupd).
    assert (Hrec : bsum (apply_tvsF bf2 r) = bsum bf2).
    { apply IH.
      rewrite (apply_ok_ext r (fun a => flook Nat.eqb bf2 a)
                 (bupd (bupd (fun a => flook Nat.eqb bf a) s
                          ((fun a => flook Nat.eqb bf a) s - amt)) d
                       (bupd (fun a => flook Nat.eqb bf a) s
                          ((fun a => flook Nat.eqb bf a) s - amt) d + amt))).
      - exact Hok.
      - intros a. unfold bf2, bf1.
        rewrite (flook_fupd nat Nat.eqb neqb_spec).
        rewrite (flook_fupd nat Nat.eqb neqb_spec).
        unfold bupd. cbn.
        rewrite (flook_fupd nat Nat.eqb neqb_spec).
        destruct (a =? d); destruct (a =? s); destruct (d =? s); reflexivity. }
    unfold bsum in *. lia.
Qed.

Theorem supply_conservation :
  forall ts mf,
    bsum (bkF (fst (seq_execrF mf ts))) = bsum (bkF mf).
Proof.
  induction ts as [| i rest IH]; intros mf.
  - reflexivity.
  - cbn [seq_execrF].
    assert (Hstep : bsum (bkF (fst (stepF mf i))) = bsum (bkF mf)).
    { destruct mf as [[stf bkf] nmf]. destruct i as [[[fee t] g] p].
      unfold stepF.
      destruct (g * p <=? flook Nat.eqb bkf fee) eqn:Hgate.
      - apply Nat.leb_le in Hgate.
        set (o := runt (fee, t, g, p)
                    (fun _ kk => flook keqb stf kk)
                    (fun _ a => flook Nat.eqb bkf a)
                    (fun _ a => flook Nat.eqb nmf a)) in *.
        assert (Hbag : forall a v, In (a, v) (o_blog o) ->
                    flook Nat.eqb bkf a = v).
        { apply bvalid_true_In.
          unfold o, runt. cbv beta iota zeta.
          apply (bvalid_self_b g g fee t
                   (fun _ kk => flook keqb stf kk)
                   (fun a => flook Nat.eqb bkf a)
                   (fun _ a => flook Nat.eqb nmf a)
                   0 0 0 [] zerof (deb0 fee (g * p))). }
        assert (Hinv0 : inflight_inv (fun a => flook Nat.eqb bkf a)
                          (bupd (fun a => flook Nat.eqb bkf a) fee
                             (flook Nat.eqb bkf fee - g * p))
                          zerof (deb0 fee (g * p))).
        { intros a. unfold bupd, deb0, zerof.
          destruct (a =? fee) eqn:Haf.
          - apply Nat.eqb_eq in Haf. subst a. lia.
          - lia. }
        assert (HIS := inflight_sound g g fee t
                         (fun _ kk => flook keqb stf kk)
                         (fun _ a => flook Nat.eqb bkf a)
                         (fun _ a => flook Nat.eqb nmf a)
                         0 0 0 [] zerof (deb0 fee (g * p))
                         (fun a => flook Nat.eqb bkf a)
                         (bupd (fun a => flook Nat.eqb bkf a) fee
                            (flook Nat.eqb bkf fee - g * p))
                         Hbag Hinv0).
        assert (Hokb := proj1 HIS). fold o in Hokb.
        unfold finishF. cbv zeta.
        destruct (o_ok o) eqn:Hok; cbn [bkF fst snd].
        + set (u := g - o_gas o) in *.
          set (ue := u - Nat.min (o_ref o) (u / 2)) in *.
          assert (Hue : ue <= g)
            by (eapply Nat.le_trans; apply Nat.le_sub_l).
          assert (Huep : ue * p <= g * p)
            by (apply Nat.mul_le_mono_r; lia).
          assert (Hdist : (g - ue) * p = g * p - ue * p)
            by (apply Nat.mul_sub_distr_r).
          set (b1 := fupd Nat.eqb bkf fee (flook Nat.eqb bkf fee - g * p))
            in *.
          assert (HB1 : bsum b1 + flook Nat.eqb bkf fee
                        = bsum bkf + (flook Nat.eqb bkf fee - g * p))
            by (apply bsum_fupd).
          assert (HB2 : bsum (apply_tvsF b1 (o_tvs o)) = bsum b1).
          { apply bsum_apply_tvsF.
            rewrite (apply_ok_ext (o_tvs o) (fun a => flook Nat.eqb b1 a)
                       (bupd (fun a => flook Nat.eqb bkf a) fee
                          (flook Nat.eqb bkf fee - g * p))).
            - exact Hokb.
            - intros a. unfold b1.
              rewrite (flook_fupd nat Nat.eqb neqb_spec).
              unfold bupd. reflexivity. }
          set (b2 := apply_tvsF b1 (o_tvs o)) in *.
          assert (HB3 : bsum (fupd Nat.eqb b2 fee
                                (flook Nat.eqb b2 fee + (g - ue) * p))
                          + flook Nat.eqb b2 fee
                        = bsum b2 + (flook Nat.eqb b2 fee + (g - ue) * p))
            by (apply bsum_fupd).
          set (b3 := fupd Nat.eqb b2 fee
                       (flook Nat.eqb b2 fee + (g - ue) * p)) in *.
          assert (HB4 : bsum (fupd Nat.eqb b3 CB
                                (flook Nat.eqb b3 CB + ue * p))
                          + flook Nat.eqb b3 CB
                        = bsum b3 + (flook Nat.eqb b3 CB + ue * p))
            by (apply bsum_fupd).
          lia.
        + set (u := g - o_gas o) in *.
          assert (Hu : u <= g) by (apply Nat.le_sub_l).
          assert (Hup : u * p <= g * p)
            by (apply Nat.mul_le_mono_r; lia).
          set (b1 := fupd Nat.eqb bkf fee (flook Nat.eqb bkf fee - u * p))
            in *.
          assert (HB1 : bsum b1 + flook Nat.eqb bkf fee
                        = bsum bkf + (flook Nat.eqb bkf fee - u * p))
            by (apply bsum_fupd).
          assert (HB2 : bsum (fupd Nat.eqb b1 CB
                                (flook Nat.eqb b1 CB + u * p))
                          + flook Nat.eqb b1 CB
                        = bsum b1 + (flook Nat.eqb b1 CB + u * p))
            by (apply bsum_fupd).
          lia.
      - cbn [bkF fst snd]. reflexivity. }
    destruct (stepF mf i) as [mf1 r].
    destruct (seq_execrF mf1 rest) as [mf2 rs] eqn:E2.
    assert (HI := IH mf1). rewrite E2 in HI.
    cbn [fst] in Hstep, HI |- *.
    lia.
Qed.

(** ** Gas soundness of the gate *)

Lemma pauper_rejected :
  forall st bk nm fee t g p,
    bk fee < g * p ->
    step (st, bk, nm) (fee, t, g, p) = ((st, bk, nm), (SRejected, 0, [], [], [])).
Proof.
  intros st bk nm fee t g p Hlt. unfold step.
  destruct (g * p <=? bk fee) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - reflexivity.
Qed.

End Machine.

(** ** Instantiation and executable examples

    Unit costs, a refund of two per storage clear, coinbase account 7,
    fees from account 9 funded with 100, and a small contract library:
    100 writes its own storage, 101 calls 100, 102 and 103 call each other,
    105 writes and reverts. *)

Definition C1 : costs := Costs 1 1 1 1 1 1 1 1.
Definition RX : nat := 2.
Definition CBX : addr := 7.
Definition FEE : addr := 9.

Definition CODE0 : addr -> tx :=
  fun c =>
    if c =? 100 then TWrite 0 5 TDone
    else if c =? 101 then TCall 100 (fun b => TWrite 1 (if b then 1 else 0) TDone)
    else if c =? 102 then TCall 103 (fun _ => TDone)
    else if c =? 103 then TCall 102 (fun _ => TDone)
    else if c =? 105 then TWrite 0 9 TRevert
    else TDone.

Definition om := omerge C1 RX CODE0 CBX.
Definition sq := seq_execr C1 RX CODE0 CBX.
Definition ps := prefix_specs C1 RX CODE0 CBX.
Definition dsp := dispatch C1 RX CODE0 CBX.
Definition js := jspecs C1 RX CODE0 CBX.
Definition xn := executions C1 RX CODE0 CBX.

Definition st0 : storage := fun _ => 0.
Definition bk0 : bank := fun a => if a =? FEE then 100 else 0.
Definition nm0 : nonces := fun _ => 0.
Definition m0 : mach := (st0, bk0, nm0).
Definition sp0 : spec := spec_of m0.

Definition tA : tx := TWrite 0 1 TDone.
Definition tB : tx := TRead 0 (fun v => TWrite 1 v TDone).
Definition block : list item := [(FEE, tA, 2, 1); (FEE, tB, 2, 1)].

Example conflict_detected :
  snd (om m0 block [sp0; sp0]) = 1.
Proof. vm_compute. reflexivity. Qed.

Example conflict_result_correct :
  fst (fst (fst (fst (om m0 block [sp0; sp0])))) (FEE, 1) = 1.
Proof. vm_compute. reflexivity. Qed.

Example conflict_fees_exact :
  let bkf := snd (fst (fst (fst (om m0 block [sp0; sp0])))) in
  (bkf FEE, bkf CBX) = (97, 3).
Proof. vm_compute. reflexivity. Qed.

Example torn_view_detected :
  snd (om m0 block
        [sp0; ((fun _ _ => 999), of_bank bk0, of_nonces nm0)]) = 1.
Proof. vm_compute. reflexivity. Qed.

Example perfect_speculation_free :
  snd (om m0 block (ps m0 block)) = 0.
Proof. vm_compute. reflexivity. Qed.

Example scheduler_in_order_free :
  snd (om m0 block (dsp m0 block [0; 1])) = 0.
Proof. vm_compute. reflexivity. Qed.

Example scheduler_out_of_order_detected :
  snd (om m0 block (dsp m0 block [1; 0])) = 1.
Proof. vm_compute. reflexivity. Qed.

Example retry_round_zero_conflicts :
  snd (om m0 block (js 0 m0 block)) = 1.
Proof. vm_compute. reflexivity. Qed.

Example retry_rounds_converge :
  snd (om m0 block (js 2 m0 block)) = 0.
Proof. vm_compute. reflexivity. Qed.

(** A stale balance read is a conflict; the corrected value is the true
    prefix balance under the transaction's own upfront gas hold. *)

Definition tBalW : tx := TBal FEE (fun b => TWrite 2 b TDone).

Example stale_balance_detected :
  snd (om m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)] [sp0; sp0]) = 1.
Proof. vm_compute. reflexivity. Qed.

Example stale_balance_corrected :
  fst (fst (fst (fst (om m0
      [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)] [sp0; sp0])))) (FEE, 2) = 97.
Proof. vm_compute. reflexivity. Qed.

Example balance_prefix_free :
  snd (om m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)]
       (ps m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)])) = 0.
Proof. vm_compute. reflexivity. Qed.

(** A stale nonce read is a conflict through its own validated log. *)

Definition tNon : tx := TNonce FEE (fun x => TWrite 3 x TDone).

Example stale_nonce_detected :
  snd (om m0 [(FEE, tA, 2, 1); (FEE, tNon, 2, 1)] [sp0; sp0]) = 1.
Proof. vm_compute. reflexivity. Qed.

Example nonce_read_correct :
  fst (fst (fst (fst (om m0
      [(FEE, tA, 2, 1); (FEE, tNon, 2, 1)]
      (ps m0 [(FEE, tA, 2, 1); (FEE, tNon, 2, 1)]))))) (FEE, 3) = 1.
Proof. vm_compute. reflexivity. Qed.

(** Transfers settle at the point of pay; an insufficient payment is an
    observable outcome, not an abort, and the revert idiom is a
    continuation choice. *)

Example transfer_settles :
  let res := om m0 [(FEE, TPay 5 30 (fun _ => TDone), 1, 1)] [sp0] in
  let bkf := snd (fst (fst (fst res))) in
  (bkf FEE, bkf 5, bkf CBX) = (69, 30, 1).
Proof. vm_compute. reflexivity. Qed.

Example pay_insufficient_observable :
  let res := om m0
      [(FEE, TPay 5 500 (fun b => if b then TDone else TEmit 42 TDone), 2, 1)]
      [sp0] in
  (snd (fst res), snd (fst (fst (fst res))) FEE, snd (fst (fst (fst res))) 5)
  = ([(SOk, 2, [], [42], [])], 98, 0).
Proof. vm_compute. reflexivity. Qed.

Example pay_insufficient_revert_idiom :
  let res := om m0
      [(FEE, TPay 5 500 (fun b => if b then TDone else TRevert), 2, 1)]
      [sp0] in
  (snd (fst res), snd (fst (fst (fst res))) FEE)
  = ([(SRev, 1, [], [], [])], 99).
Proof. vm_compute. reflexivity. Qed.

Example event_emitted :
  snd (fst (om m0 [(FEE, TEmit 42 TDone, 1, 1)] [sp0]))
  = [(SOk, 1, [], [42], [])].
Proof. vm_compute. reflexivity. Qed.

Example event_discarded_on_revert :
  snd (fst (om m0 [(FEE, TEmit 42 TRevert, 1, 1)] [sp0]))
  = [(SRev, 1, [], [], [])].
Proof. vm_compute. reflexivity. Qed.

Example nonce_bumps :
  snd (fst (fst (om m0 block [sp0; sp0]))) FEE = 2.
Proof. vm_compute. reflexivity. Qed.

Example pauper_pays_nothing :
  om m0 [(FEE, TWrite 0 5 TDone, 200, 1)] [sp0]
  = ((m0, [(SRejected, 0, [], [], [])]), 0).
Proof. vm_compute. reflexivity. Qed.

Example counterfeit_impossible :
  let res := om m0 [(FEE, TWrite FEE 777 TDone, 2, 1)] [sp0] in
  (fst (fst (fst (fst res))) (FEE, FEE), snd (fst (fst (fst res))) FEE)
  = (777, 99).
Proof. vm_compute. reflexivity. Qed.

(** Calls run in the callee's storage scope; a reverted frame surrenders
    its writes and keeps its gas; reentrant call cycles terminate by
    gas. *)

Example call_scoped :
  let res := om m0
      [(FEE, TCall 100 (fun b => TWrite 1 (if b then 1 else 0) TDone), 3, 1)]
      [sp0] in
  (fst (fst (fst (fst res))) (100, 0), fst (fst (fst (fst res))) (FEE, 1))
  = (5, 1).
Proof. vm_compute. reflexivity. Qed.

Example frame_revert_isolated :
  let res := om m0
      [(FEE, TCall 105 (fun b => TWrite 1 (if b then 1 else 0) TDone), 3, 1)]
      [sp0] in
  (fst (fst (fst (fst res))) (105, 0), fst (fst (fst (fst res))) (FEE, 1),
   snd (fst res))
  = (0, 0, [(SOk, 2, [((FEE, 1), 0)], [], [])]).
Proof. vm_compute. reflexivity. Qed.

Example reentrancy_terminates :
  snd (fst (om m0 [(FEE, TCall 102 (fun _ => TDone), 7, 1)] [sp0]))
  = [(SOk, 7, [], [], [])].
Proof. vm_compute. reflexivity. Qed.

(** Refunds accrue on storage clears and are capped at half the
    consumption. *)

Example refund_capped :
  let res := om m0
      [(FEE, TWrite 0 1 (TWrite 1 1 (TWrite 2 1 (TWrite 3 1
                (TWrite 0 0 TDone)))), 5, 1)] [sp0] in
  (snd (fst (fst (fst res))) FEE,
   fst (fst (fst (fst res))) (FEE, 0))
  = (97, 0).
Proof. vm_compute. reflexivity. Qed.

Example loop_terminates_with_refund :
  let res := om m0
      [(FEE, TWrite 0 3 (TWhile 0 (TRead 0 (fun v => TWrite 0 (pred v) TDone))
                                TDone), 11, 1)] [sp0] in
  (fst (fst (fst (fst res))) (FEE, 0), snd (fst (fst (fst res))) FEE)
  = (0, 91).
Proof. vm_compute. reflexivity. Qed.

Example spin_reverts_charged :
  let res := om m0 [(FEE, TWrite 0 1 (TWhile 0 TDone TDone), 5, 1)] [sp0] in
  (fst (fst (fst (fst res))) (FEE, 0), snd (fst (fst (fst res))) FEE,
   snd (fst res))
  = (0, 95, [(SRev, 5, [], [], [])]).
Proof. vm_compute. reflexivity. Qed.

(** The operational scheduler: out-of-order execution, then commits;
    receipts land sequential. *)

Example op_replay :
  let s := reach C1 RX CODE0 CBX block (oinit m0)
             [AExec 1; AExec 0; ACommit; ACommit] in
  (os_c s, os_rs s) = (2, snd (sq m0 block)).
Proof. vm_compute. reflexivity. Qed.

(** The static footprint theorem in action: certificates are discharged by
    constructors on the syntax alone. *)

Example static_two_writes :
  snd (om m0 [(FEE, tA, 2, 1); (FEE, TWrite 3 7 TDone, 2, 1)]
        (map (fun _ => spec_of m0)
             [(FEE, tA, 2, 1); (FEE, TWrite 3 7 TDone, 2, 1)])) = 0.
Proof.
  apply (static_disjoint_free C1 RX CODE0 CBX
           [(FEE, tA, 2, 1); (FEE, TWrite 3 7 TDone, 2, 1)]
           [[]; []] [[(FEE, 0)]; [(FEE, 3)]] st0 bk0 nm0).
  - reflexivity.
  - reflexivity.
  - intros j i FR FW H1 H2 H3.
    destruct j as [| [| j]]; cbn in H1, H2, H3.
    + injection H1 as <-. injection H2 as <-. injection H3 as <-.
      cbn. constructor; [cbn; auto | constructor].
    + injection H1 as <-. injection H2 as <-. injection H3 as <-.
      cbn. constructor; [cbn; auto | constructor].
    + destruct j; discriminate H1.
  - intros j k FWj FRk Hjk H1 H2.
    destruct k as [| [| k]]; cbn in H2.
    + lia.
    + injection H2 as <-. intros kk _ Hin. destruct Hin.
    + destruct k; discriminate H2.
Qed.

(** ** Randomized cross-validation

    A linear-congruential generator drives random blocks, random torn
    speculations, and a checker comparing the merge against sequential
    execution on receipts, sampled storage, bank, and nonces, together
    with the work law, the per-position flags, and the money ledger.
    Three hundred seeds are checked by computation. *)

Local Open Scope N_scope.
Definition lcg (s : N) : N := (1103515245 * s + 12345) mod 2147483648.
Definition mix (s x : N) : N := lcg (s + 2654435761 * x).
Local Close Scope N_scope.
Definition nof (x : N) (m : nat) : nat :=
  N.to_nat (N.modulo x (N.of_nat m)).

Fixpoint gtx (fuel : nat) (s : N) : tx :=
  match fuel with
  | 0 => TDone
  | S f =>
      match nof s 8 with
      | 0 => TWrite (nof (lcg s) 3) (nof (lcg (lcg s)) 3) (gtx f (mix s 3))
      | 1 => TRead (nof (lcg s) 3) (fun v => gtx f (mix s (N.of_nat v)))
      | 2 => TBal (8 + nof (lcg s) 2) (fun b => gtx f (mix s (N.of_nat b)))
      | 3 => TNonce (8 + nof (lcg s) 2) (fun x => gtx f (mix s (N.of_nat x)))
      | 4 => TEmit (nof (lcg s) 5) (gtx f (mix s 5))
      | 5 => TPay (nof (lcg s) 4) (nof (lcg (lcg s)) 40)
                  (fun b => gtx f (mix s (if b then 7 else 11)))
      | 6 => TCall (100 + nof (lcg s) 2)
                   (fun b => gtx f (mix s (if b then 13 else 17)))
      | _ => TWhile (nof (lcg s) 3) (TWrite (nof (lcg (lcg s)) 3) 0 TDone)
                    (gtx f (mix s 19))
      end
  end.

Definition bkH : bank :=
  fun a => if a =? 9 then 100 else if a =? 8 then 10 else 0.
Definition mH : mach := (st0, bkH, nm0).

Definition gitem (s : N) : item :=
  (8 + nof s 2, gtx 4 (lcg s), 8 + nof (lcg s) 8, nof (lcg (lcg s)) 2).

Definition gblock (s : N) : list item :=
  [gitem (mix s 101); gitem (mix s 202); gitem (mix s 303)].

Definition gspec (s : N) : spec :=
  match nof s 3 with
  | 0 => spec_of mH
  | 1 => ((fun n kk => nof (mix s (N.of_nat (n + fst kk * 7 + snd kk * 13))) 4),
          (fun n a => nof (mix s (N.of_nat (n + a * 3))) 50),
          (fun n a => nof (mix s (N.of_nat (n + a * 5))) 3))
  | _ => ((fun _ kk => nof (mix s (N.of_nat (fst kk + snd kk))) 4),
          of_bank bkH, of_nonces nm0)
  end.

Definition gspecs (s : N) : list spec :=
  [gspec (mix s 11); gspec (mix s 22); gspec (mix s 33)].

Definition beq_status (a b : status) : bool :=
  match a, b with
  | SOk, SOk | SRev, SRev | SRejected, SRejected => true
  | _, _ => false
  end.

Fixpoint beq_ln (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && beq_ln a' b'
  | _, _ => false
  end.

Fixpoint beq_buf (a b : buffer) : bool :=
  match a, b with
  | [], [] => true
  | (k1, v1) :: a', (k2, v2) :: b' =>
      keqb k1 k2 && (v1 =? v2) && beq_buf a' b'
  | _, _ => false
  end.

Fixpoint beq_tvs (a b : list transfer) : bool :=
  match a, b with
  | [], [] => true
  | (s1, d1, x1) :: a', (s2, d2, x2) :: b' =>
      (s1 =? s2) && (d1 =? d2) && (x1 =? x2) && beq_tvs a' b'
  | _, _ => false
  end.

Definition beq_rcpt (a b : rcpt) : bool :=
  let '(sa, ua, wa, ea, ta) := a in
  let '(sb, ub, wb, eb, tb) := b in
  beq_status sa sb && (ua =? ub) && beq_buf wa wb && beq_ln ea eb
  && beq_tvs ta tb.

Fixpoint beq_rs (a b : list rcpt) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => beq_rcpt x y && beq_rs a' b'
  | _, _ => false
  end.

Definition sample_addrs : list addr :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 100; 101; 102; 103; 105].

Definition sample_keys : list key :=
  list_prod sample_addrs [0; 1; 2; 3].

Definition beq_st (s1 s2 : storage) : bool :=
  forallb (fun kk => s1 kk =? s2 kk) sample_keys.

Definition beq_bk (b1 b2 : bank) : bool :=
  forallb (fun a => b1 a =? b2 a) sample_addrs.

Definition check (sd : nat) : bool :=
  let s := N.of_nat sd in
  let ts := gblock s in
  let specs := gspecs s in
  let '(mm, rs, cnt) := om mH ts specs in
  let '(ms, rss) := sq mH ts in
  beq_rs rs rss
  && beq_st (fst (fst mm)) (fst (fst ms))
  && beq_bk (snd (fst mm)) (snd (fst ms))
  && beq_bk (snd mm) (snd ms)
  && (xn mH ts specs =? nonrejected rss + cnt)
  && (cnt =? count_true (reexec_flags C1 RX CODE0 CBX mH ts specs))
  && forallb (fun f => snd (fst mm) f + debits f ts rss
                       =? bkH f + credits CBX f ts rss)
             sample_addrs.

Lemma harness_300 : forallb check (seq 0 300) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Assumption audit *)

Print Assumptions optimistic_correct.
Print Assumptions fast_path.
Print Assumptions reexec_bound.
Print Assumptions reexec_per_tx.
Print Assumptions executions_law.
Print Assumptions work_upper.
Print Assumptions work_lower.
Print Assumptions speculation_irrelevant.
Print Assumptions scheduler_correct.
Print Assumptions dispatch_in_order.
Print Assumptions scheduler_in_order_optimal.
Print Assumptions work_inorder.
Print Assumptions dispatch_complete.
Print Assumptions retry_progress.
Print Assumptions retry_converges.
Print Assumptions retry_round_progress.
Print Assumptions retry_loop_converges.
Print Assumptions jmach_progress.
Print Assumptions money_conservation.
Print Assumptions omerge_money_conservation.
Print Assumptions nonce_law.
Print Assumptions apply_law.
Print Assumptions runp_gas_bound.
Print Assumptions replay.
Print Assumptions inflight_sound.
Print Assumptions pauper_rejected.
Print Assumptions fp_sound.
Print Assumptions static_disjoint_free.
Print Assumptions work_disjoint.
Print Assumptions estimated_order_free.
Print Assumptions level_rounds_bound.
Print Assumptions level_rounds_converge.
Print Assumptions op_safety.
Print Assumptions op_liveness.
Print Assumptions engine_seq_correct.
Print Assumptions engine_merge_correct.
Print Assumptions supply_conservation.
Print Assumptions harness_300.

(** ** Extraction of the engine *)

From Stdlib Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "occ_engine.ml"
  seq_execrF omergeF stepF finishF flook fupd commitF apply_tvsF.
