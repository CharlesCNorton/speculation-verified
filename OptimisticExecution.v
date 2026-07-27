(******************************************************************************)
(*                                                                            *)
(*                 Optimistic Parallel Transaction Execution                  *)
(*                                                                            *)
(*     Optimistic concurrency control over a linearly ordered block of        *)
(*     transactions: speculative runs against arbitrary read sources,         *)
(*     ordered commit-time validation by storage and balance read logs,       *)
(*     re-execution on conflict. Machine-checked safety, scheduler            *)
(*     optimality, retry convergence, conflict freedom, and gas,              *)
(*     transfer, and nonce ledgers.                                           *)
(*                                                                            *)
(*     Reference: Kung HT, Robinson JT. On optimistic methods for             *)
(*     concurrency control. ACM TODS. 1981;6(2):213-226.                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: July 26, 2026                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(** ** Storage, bank, nonces *)

Definition addr : Type := nat.
Definition val : Type := nat.
Definition storage : Type := addr -> val.
Definition bank : Type := addr -> nat.

Definition upd (s : storage) (a : addr) (v : val) : storage :=
  fun a' => if Nat.eqb a' a then v else s a'.

Definition bupd (b : bank) (a : addr) (n : nat) : bank :=
  fun a' => if Nat.eqb a' a then n else b a'.

Lemma bupd_same : forall b a n, bupd b a n a = n.
Proof. intros. unfold bupd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma bupd_other : forall b a n a', a' <> a -> bupd b a n a' = b a'.
Proof.
  intros b a n a' H. unfold bupd.
  apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Definition buffer : Type := list (addr * val).

Fixpoint wlookup (w : buffer) (a : addr) : option val :=
  match w with
  | [] => None
  | (a', v) :: rest => if Nat.eqb a a' then Some v else wlookup rest a
  end.

Definition commit (s : storage) (w : buffer) : storage :=
  fold_right (fun p s' => upd s' (fst p) (snd p)) s w.

(** ** Transfer settlement

    Transfers settle in order against the bank; any insufficient debit fails
    the whole settlement. *)

Definition transfer : Type := (addr * nat)%type.

Fixpoint settle (b : bank) (s : addr) (l : list transfer) : option bank :=
  match l with
  | [] => Some b
  | (d, amt) :: r =>
      if Nat.leb amt (b s)
      then settle (bupd (bupd b s (b s - amt)) d
                        (bupd b s (b s - amt) d + amt)) s r
      else None
  end.

Fixpoint outsum (l : list transfer) : nat :=
  match l with
  | [] => 0
  | (_, amt) :: r => amt + outsum r
  end.

Fixpoint insum (f : addr) (l : list transfer) : nat :=
  match l with
  | [] => 0
  | (d, amt) :: r => (if Nat.eqb d f then amt else 0) + insum f r
  end.

(** Settlement is an exact ledger: what leaves the sender arrives at the
    destinations, account by account. *)

Lemma settle_law :
  forall l b s b',
    settle b s l = Some b' ->
    forall f,
      b' f + (if Nat.eqb s f then outsum l else 0)
      = b f + insum f l.
Proof.
  induction l as [| [d amt] r IH]; simpl; intros b s b' Hs f.
  - injection Hs as <-. destruct (Nat.eqb s f); lia.
  - destruct (Nat.leb amt (b s)) eqn:Hle; [| discriminate].
    apply Nat.leb_le in Hle.
    set (b1 := bupd b s (b s - amt)).
    set (b2 := bupd b1 d (b1 d + amt)).
    specialize (IH b2 s b' Hs f).
    destruct (Nat.eqb d f) eqn:Hdf; destruct (Nat.eqb s f) eqn:Hsf;
      try rewrite Hsf in IH; cbn beta iota in IH; cbn beta iota.
    + apply Nat.eqb_eq in Hdf. apply Nat.eqb_eq in Hsf. subst d s.
      assert (Hb2 : b2 f = b f).
      { unfold b2. rewrite bupd_same.
        unfold b1. rewrite bupd_same. lia. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_eq in Hdf. apply Nat.eqb_neq in Hsf. subst d.
      assert (Hb2 : b2 f = b f + amt).
      { unfold b2. rewrite bupd_same.
        unfold b1.
        rewrite (bupd_other b s (b s - amt) f) by congruence. reflexivity. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_neq in Hdf. apply Nat.eqb_eq in Hsf. subst s.
      assert (Hb2 : b2 f = b f - amt).
      { unfold b2.
        rewrite (bupd_other b1 d (b1 d + amt) f) by congruence.
        unfold b1. rewrite bupd_same. reflexivity. }
      rewrite Hb2 in IH. lia.
    + apply Nat.eqb_neq in Hdf. apply Nat.eqb_neq in Hsf.
      assert (Hb2 : b2 f = b f).
      { unfold b2.
        rewrite (bupd_other b1 d (b1 d + amt) f) by congruence.
        unfold b1.
        rewrite (bupd_other b s (b s - amt) f) by congruence. reflexivity. }
      rewrite Hb2 in IH. lia.
Qed.

(** ** Transactions

    [TBal] reads an account balance; balance reads observe the prefix bank
    and are logged and validated like storage reads, through their own
    log. *)

Inductive tx : Type :=
| TDone   : tx
| TRevert : tx
| TWrite  : addr -> val -> tx -> tx
| TRead   : addr -> (val -> tx) -> tx
| TBal    : addr -> (nat -> tx) -> tx
| TWhile  : addr -> tx -> tx -> tx
| TEmit   : val -> tx -> tx
| TPay    : addr -> nat -> tx -> tx.

Fixpoint tseq (t1 t2 : tx) : tx :=
  match t1 with
  | TDone => t2
  | TRevert => TRevert
  | TWrite a v k => TWrite a v (tseq k t2)
  | TRead a k => TRead a (fun v => tseq (k v) t2)
  | TBal a k => TBal a (fun v => tseq (k v) t2)
  | TWhile a b k => TWhile a b (tseq k t2)
  | TEmit e k => TEmit e (tseq k t2)
  | TPay d amt k => TPay d amt (tseq k t2)
  end.

Fixpoint trepeat (n : nat) (body : tx) : tx :=
  match n with
  | 0 => TDone
  | S m => tseq body (trepeat m body)
  end.

(** A block item: fee account (also the transfer sender and nonce owner),
    the transaction, its gas limit, and its gas price. *)

Definition item : Type := (addr * tx * nat * nat)%type.

(** ** Execution over read sources *)

Definition reader : Type := nat -> addr -> val.
Definition breader : Type := nat -> addr -> nat.

Definition of_state (s : storage) : reader := fun _ a => s a.
Definition of_bank (b : bank) : breader := fun _ a => b a.

(** An outcome: storage read log, balance read log, write buffer, events,
    declared transfers, completion flag, gas consumed. *)

Definition outcome : Type :=
  (list (addr * val) * list (addr * nat) * buffer * list val * list transfer
   * bool * nat)%type.

Definition o_log (o : outcome) : list (addr * val) :=
  let '(l, _, _, _, _, _, _) := o in l.
Definition o_blog (o : outcome) : list (addr * nat) :=
  let '(_, bl, _, _, _, _, _) := o in bl.
Definition o_buf (o : outcome) : buffer :=
  let '(_, _, w, _, _, _, _) := o in w.

Fixpoint runp (g : nat) (t : tx) (rd : reader) (brd : breader)
              (n bn : nat) (w : buffer) : outcome :=
  match t with
  | TDone => ([], [], w, [], [], true, 0)
  | TRevert => ([], [], w, [], [], false, 0)
  | TWrite a v k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          let '(slog, blog, w', evs, tvs, ok, u) :=
            runp g' k rd brd n bn ((a, v) :: w) in
          (slog, blog, w', evs, tvs, ok, S u)
      end
  | TRead a k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          match wlookup w a with
          | Some v =>
              let '(slog, blog, w', evs, tvs, ok, u) :=
                runp g' (k v) rd brd n bn w in
              (slog, blog, w', evs, tvs, ok, S u)
          | None =>
              let v := rd n a in
              let '(slog, blog, w', evs, tvs, ok, u) :=
                runp g' (k v) rd brd (S n) bn w in
              ((a, v) :: slog, blog, w', evs, tvs, ok, S u)
          end
      end
  | TBal a k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          let v := brd bn a in
          let '(slog, blog, w', evs, tvs, ok, u) :=
            runp g' (k v) rd brd n (S bn) w in
          (slog, (a, v) :: blog, w', evs, tvs, ok, S u)
      end
  | TWhile a b k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          match wlookup w a with
          | Some v =>
              let '(slog, blog, w', evs, tvs, ok, u) :=
                if Nat.eqb v 0
                then runp g' k rd brd n bn w
                else runp g' (tseq b (TWhile a b k)) rd brd n bn w in
              (slog, blog, w', evs, tvs, ok, S u)
          | None =>
              let v := rd n a in
              let '(slog, blog, w', evs, tvs, ok, u) :=
                if Nat.eqb v 0
                then runp g' k rd brd (S n) bn w
                else runp g' (tseq b (TWhile a b k)) rd brd (S n) bn w in
              ((a, v) :: slog, blog, w', evs, tvs, ok, S u)
          end
      end
  | TEmit e k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          let '(slog, blog, w', evs, tvs, ok, u) :=
            runp g' k rd brd n bn w in
          (slog, blog, w', e :: evs, tvs, ok, S u)
      end
  | TPay d amt k =>
      match g with
      | 0 => ([], [], w, [], [], false, 0)
      | S g' =>
          let '(slog, blog, w', evs, tvs, ok, u) :=
            runp g' k rd brd n bn w in
          (slog, blog, w', evs, (d, amt) :: tvs, ok, S u)
      end
  end.

(** ** Gas bound *)

Lemma runp_gas_bound :
  forall g t rd brd n bn w slog blog w' evs tvs ok u,
    runp g t rd brd n bn w = (slog, blog, w', evs, tvs, ok, u) ->
    u <= g.
Proof.
  induction g as [| g' IH]; intros t rd brd n bn w slog blog w' evs tvs ok u;
    destruct t as [| | a v k | a k | a k | a tb k | e k | d amt k]; simpl;
    intros Hrun; try (injection Hrun as _ _ _ _ _ _ <-; lia).
  - destruct (runp g' k rd brd n bn ((a, v) :: w))
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ _ _ _ _ _ <-.
    apply le_n_S. eapply IH. exact Hrec.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (runp g' (k v0) rd brd n bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as _ _ _ _ _ _ <-.
      apply le_n_S. eapply IH. exact Hrec.
    + destruct (runp g' (k (rd n a)) rd brd (S n) bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as _ _ _ _ _ _ <-.
      apply le_n_S. eapply IH. exact Hrec.
  - destruct (runp g' (k (brd bn a)) rd brd n (S bn) w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ _ _ _ _ _ <-.
    apply le_n_S. eapply IH. exact Hrec.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (Nat.eqb v0 0) eqn:Hz.
      * destruct (runp g' k rd brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ _ _ _ _ _ <-.
        apply le_n_S. eapply IH. exact Hrec.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ _ _ _ _ _ <-.
        apply le_n_S. eapply IH. exact Hrec.
    + destruct (Nat.eqb (rd n a) 0) eqn:Hz.
      * destruct (runp g' k rd brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ _ _ _ _ _ <-.
        apply le_n_S. eapply IH. exact Hrec.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ _ _ _ _ _ <-.
        apply le_n_S. eapply IH. exact Hrec.
  - destruct (runp g' k rd brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ _ _ _ _ _ <-.
    apply le_n_S. eapply IH. exact Hrec.
  - destruct (runp g' k rd brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ _ _ _ _ _ <-.
    apply le_n_S. eapply IH. exact Hrec.
Qed.

(** ** Validation lemmas *)

Fixpoint valid (s : storage) (log : list (addr * val)) : bool :=
  match log with
  | [] => true
  | (a, v) :: rest => Nat.eqb (s a) v && valid s rest
  end.

Fixpoint bvalid (b : bank) (blog : list (addr * nat)) : bool :=
  match blog with
  | [] => true
  | (a, v) :: rest => Nat.eqb (b a) v && bvalid b rest
  end.

Lemma valid_true_In :
  forall log s,
    valid s log = true ->
    forall a v, In (a, v) log -> s a = v.
Proof.
  induction log as [| [a0 v0] rest IH]; simpl; intros s H a v Hin.
  - contradiction.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    destruct Hin as [Hin | Hin].
    + injection Hin as -> ->. apply Nat.eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma bvalid_true_In :
  forall blog b,
    bvalid b blog = true ->
    forall a v, In (a, v) blog -> b a = v.
Proof.
  induction blog as [| [a0 v0] rest IH]; simpl; intros b H a v Hin.
  - contradiction.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    destruct Hin as [Hin | Hin].
    + injection Hin as -> ->. apply Nat.eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

(** Replay: a storage and bank agreeing with every logged read reproduce the
    run exactly, logs, buffer, events, transfers, revert decision, and gas,
    whatever the readers were. *)

Lemma replay :
  forall g t rd brd n bn (s : storage) (b : bank) w slog blog w' evs tvs ok u,
    runp g t rd brd n bn w = (slog, blog, w', evs, tvs, ok, u) ->
    (forall a v, In (a, v) slog -> s a = v) ->
    (forall a v, In (a, v) blog -> b a = v) ->
    forall m bm,
      runp g t (of_state s) (of_bank b) m bm w
      = (slog, blog, w', evs, tvs, ok, u).
Proof.
  induction g as [| g' IH]; intros t rd brd n bn s b w slog blog w' evs tvs ok u;
    destruct t as [| | a v k | a k | a k | a tb k | e k | d amt k]; simpl;
    intros Hrun Hags Hagb m bm; try exact Hrun.
  - destruct (runp g' k rd brd n bn ((a, v) :: w))
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- <- <- <- <- <- <-.
    rewrite (IH k rd brd n bn s b ((a, v) :: w)
                slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
    reflexivity.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (runp g' (k v0) rd brd n bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as <- <- <- <- <- <- <-.
      rewrite (IH (k v0) rd brd n bn s b w
                  slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
      reflexivity.
    + destruct (runp g' (k (rd n a)) rd brd (S n) bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as <- <- <- <- <- <- <-.
      assert (Hsa : s a = rd n a) by (apply Hags; left; reflexivity).
      replace (of_state s m a) with (rd n a) by (symmetry; exact Hsa).
      assert (Htail : forall a' v', In (a', v') slog0 -> s a' = v').
      { intros a' v' Hin. apply Hags. right. exact Hin. }
      rewrite (IH (k (rd n a)) rd brd (S n) bn s b w
                  slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Htail Hagb (S m) bm).
      reflexivity.
  - destruct (runp g' (k (brd bn a)) rd brd n (S bn) w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- <- <- <- <- <- <-.
    assert (Hba : b a = brd bn a) by (apply Hagb; left; reflexivity).
    replace (of_bank b bm a) with (brd bn a) by (symmetry; exact Hba).
    assert (Hbtail : forall a' v', In (a', v') blog0 -> b a' = v').
    { intros a' v' Hin. apply Hagb. right. exact Hin. }
    rewrite (IH (k (brd bn a)) rd brd n (S bn) s b w
                slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hbtail m (S bm)).
    reflexivity.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (Nat.eqb v0 0) eqn:Hz.
      * destruct (runp g' k rd brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- <- <- <- <- <- <-.
        rewrite (IH k rd brd n bn s b w
                    slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
        reflexivity.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- <- <- <- <- <- <-.
        rewrite (IH (tseq tb (TWhile a tb k)) rd brd n bn s b w
                    slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
        reflexivity.
    + destruct (Nat.eqb (rd n a) 0) eqn:Hz.
      * destruct (runp g' k rd brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- <- <- <- <- <- <-.
        assert (Hsa : s a = rd n a) by (apply Hags; left; reflexivity).
        replace (of_state s m a) with (rd n a) by (symmetry; exact Hsa).
        rewrite Hz.
        assert (Htail : forall a' v', In (a', v') slog0 -> s a' = v').
        { intros a' v' Hin. apply Hags. right. exact Hin. }
        rewrite (IH k rd brd (S n) bn s b w
                    slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Htail Hagb (S m) bm).
        reflexivity.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- <- <- <- <- <- <-.
        assert (Hsa : s a = rd n a) by (apply Hags; left; reflexivity).
        replace (of_state s m a) with (rd n a) by (symmetry; exact Hsa).
        rewrite Hz.
        assert (Htail : forall a' v', In (a', v') slog0 -> s a' = v').
        { intros a' v' Hin. apply Hags. right. exact Hin. }
        rewrite (IH (tseq tb (TWhile a tb k)) rd brd (S n) bn s b w
                    slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Htail Hagb (S m) bm).
        reflexivity.
  - destruct (runp g' k rd brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- <- <- <- <- <- <-.
    rewrite (IH k rd brd n bn s b w
                slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
    reflexivity.
  - destruct (runp g' k rd brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- <- <- <- <- <- <-.
    rewrite (IH k rd brd n bn s b w
                slog0 blog0 w0 evs0 tvs0 ok0 u0 Hrec Hags Hagb m bm).
    reflexivity.
Qed.

(** Self-validation, one side at a time: a run whose storage reads come from
    a storage records exactly the values it holds, whatever the bank reader
    was, and symmetrically for the bank.  The asymmetry is deliberate: each
    log certifies its own read source independently. *)

Lemma valid_self_s :
  forall g t (s : storage) (brd : breader) n bn w slog blog w' evs tvs ok u,
    runp g t (of_state s) brd n bn w = (slog, blog, w', evs, tvs, ok, u) ->
    valid s slog = true.
Proof.
  induction g as [| g' IH]; intros t s brd n bn w slog blog w' evs tvs ok u;
    destruct t as [| | a v k | a k | a k | a tb k | e k | d amt k]; simpl;
    intros Hrun;
    try (injection Hrun as <- _ _ _ _ _ _; reflexivity).
  - destruct (runp g' k (of_state s) brd n bn ((a, v) :: w))
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- _ _ _ _ _ _.
    eapply IH; eassumption.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (runp g' (k v0) (of_state s) brd n bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as <- _ _ _ _ _ _.
      eapply IH; eassumption.
    + destruct (runp g' (k (of_state s n a)) (of_state s) brd (S n) bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as <- _ _ _ _ _ _.
      simpl. rewrite Nat.eqb_refl. simpl.
      eapply IH; eassumption.
  - destruct (runp g' (k (brd bn a)) (of_state s) brd n (S bn) w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- _ _ _ _ _ _.
    eapply IH; eassumption.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (Nat.eqb v0 0) eqn:Hz.
      * destruct (runp g' k (of_state s) brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- _ _ _ _ _ _.
        eapply IH; eassumption.
      * destruct (runp g' (tseq tb (TWhile a tb k)) (of_state s) brd n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- _ _ _ _ _ _.
        eapply IH; eassumption.
    + destruct (Nat.eqb (of_state s n a) 0) eqn:Hz.
      * destruct (runp g' k (of_state s) brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- _ _ _ _ _ _.
        simpl. rewrite Nat.eqb_refl. simpl.
        eapply IH; eassumption.
      * destruct (runp g' (tseq tb (TWhile a tb k)) (of_state s) brd (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as <- _ _ _ _ _ _.
        simpl. rewrite Nat.eqb_refl. simpl.
        eapply IH; eassumption.
  - destruct (runp g' k (of_state s) brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- _ _ _ _ _ _.
    eapply IH; eassumption.
  - destruct (runp g' k (of_state s) brd n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as <- _ _ _ _ _ _.
    eapply IH; eassumption.
Qed.

Lemma bvalid_self_b :
  forall g t (rd : reader) (b : bank) n bn w slog blog w' evs tvs ok u,
    runp g t rd (of_bank b) n bn w = (slog, blog, w', evs, tvs, ok, u) ->
    bvalid b blog = true.
Proof.
  induction g as [| g' IH]; intros t rd b n bn w slog blog w' evs tvs ok u;
    destruct t as [| | a v k | a k | a k | a tb k | e k | d amt k]; simpl;
    intros Hrun;
    try (injection Hrun as _ <- _ _ _ _ _; reflexivity).
  - destruct (runp g' k rd (of_bank b) n bn ((a, v) :: w))
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ <- _ _ _ _ _.
    eapply IH; eassumption.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (runp g' (k v0) rd (of_bank b) n bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as _ <- _ _ _ _ _.
      eapply IH; eassumption.
    + destruct (runp g' (k (rd n a)) rd (of_bank b) (S n) bn w)
        as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
      injection Hrun as _ <- _ _ _ _ _.
      eapply IH; eassumption.
  - destruct (runp g' (k (of_bank b bn a)) rd (of_bank b) n (S bn) w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ <- _ _ _ _ _.
    simpl. rewrite Nat.eqb_refl. simpl.
    eapply IH; eassumption.
  - destruct (wlookup w a) as [v0 |] eqn:Hw.
    + destruct (Nat.eqb v0 0) eqn:Hz.
      * destruct (runp g' k rd (of_bank b) n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ <- _ _ _ _ _.
        eapply IH; eassumption.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd (of_bank b) n bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ <- _ _ _ _ _.
        eapply IH; eassumption.
    + destruct (Nat.eqb (rd n a) 0) eqn:Hz.
      * destruct (runp g' k rd (of_bank b) (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ <- _ _ _ _ _.
        eapply IH; eassumption.
      * destruct (runp g' (tseq tb (TWhile a tb k)) rd (of_bank b) (S n) bn w)
          as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
        injection Hrun as _ <- _ _ _ _ _.
        eapply IH; eassumption.
  - destruct (runp g' k rd (of_bank b) n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ <- _ _ _ _ _.
    eapply IH; eassumption.
  - destruct (runp g' k rd (of_bank b) n bn w)
      as [[[[[[slog0 blog0] w0] evs0] tvs0] ok0] u0] eqn:Hrec.
    injection Hrun as _ <- _ _ _ _ _.
    eapply IH; eassumption.
Qed.

(** ** Conflict-freedom mechanism *)

Lemma valid_stable :
  forall log s s',
    valid s log = true ->
    (forall a, In a (map fst log) -> s' a = s a) ->
    valid s' log = true.
Proof.
  induction log as [| [a0 v0] rest IH]; simpl; intros s s' H Hag.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff. split.
    + rewrite (Hag a0 (or_introl eq_refl)). exact H1.
    + eapply IH; [exact H2 |].
      intros a Hin. apply Hag. right. exact Hin.
Qed.

Lemma commit_untouched :
  forall w s a,
    ~ In a (map fst w) ->
    commit s w a = s a.
Proof.
  induction w as [| [a0 v0] w' IH]; simpl; intros s a Hnin.
  - reflexivity.
  - unfold upd. destruct (Nat.eqb a a0) eqn:He.
    + apply Nat.eqb_eq in He. subst. exfalso. apply Hnin. left. reflexivity.
    + apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

(** ** Machine, receipts, and the gated step

    Everything below is parameterized by the coinbase account [CB], which
    receives gas payments. *)

Notation nonces := bank (only parsing).
Definition mach : Type := (storage * bank * nonces)%type.

Inductive status : Type := SOk | SRev | SRejected.

Definition rcpt : Type :=
  (status * nat * buffer * list val * list transfer)%type.

Section WithCoinbase.

Variable CB : addr.

(** The gate compares the gas cost ceiling [g * p] against the fee balance.
    An executed transaction pays [u * p] to the coinbase and bumps its
    nonce; a completing transaction additionally settles its transfers, and
    settlement failure reverts it.  Reverted and rejected transactions leave
    no writes, events, or transfers. *)

Definition finish (st : storage) (bk : bank) (nm : nonces)
                  (fee : addr) (g p : nat)
                  (w : buffer) (evs : list val) (tvs : list transfer)
                  (ok : bool) (u : nat) : mach * rcpt :=
  if Nat.leb (g * p) (bk fee)
  then
    if ok
    then
      match settle (bupd (bupd bk fee (bk fee - u * p)) CB
                         (bupd bk fee (bk fee - u * p) CB + u * p))
                   fee (rev tvs) with
      | Some bk3 =>
          ((commit st w, bk3, bupd nm fee (S (nm fee))),
           (SOk, u, w, evs, rev tvs))
      | None =>
          ((st, bupd (bupd bk fee (bk fee - u * p)) CB
                     (bupd bk fee (bk fee - u * p) CB + u * p),
            bupd nm fee (S (nm fee))),
           (SRev, u, [], [], []))
      end
    else ((st, bupd (bupd bk fee (bk fee - u * p)) CB
                    (bupd bk fee (bk fee - u * p) CB + u * p),
           bupd nm fee (S (nm fee))),
          (SRev, u, [], [], []))
  else ((st, bk, nm), (SRejected, 0, [], [], [])).

Definition step (m : mach) (i : item) : mach * rcpt :=
  let '(st, bk, nm) := m in
  let '(fee, t, g, p) := i in
  let '(_, _, w, evs, tvs, ok, u) := runp g t (of_state st) (of_bank bk) 0 0 [] in
  finish st bk nm fee g p w evs tvs ok u.

Fixpoint seq_execr (m : mach) (ts : list item) : mach * list rcpt :=
  match ts with
  | [] => (m, [])
  | i :: rest =>
      let '(m1, r) := step m i in
      let '(m2, rs) := seq_execr m1 rest in
      (m2, r :: rs)
  end.

(** ** Validation and merge

    A speculation is a pair of read sources, storage and bank; validation
    checks the storage log against the merged prefix storage and the balance
    log against the merged prefix bank. *)

Definition spec : Type := (reader * breader)%type.

Fixpoint omerge (m : mach) (ts : list item) (specs : list spec)
  : mach * list rcpt * nat :=
  match ts with
  | [] => (m, [], 0)
  | i :: rest =>
      match specs with
      | sp :: sps =>
          let '(fee, t, g, p) := i in
          let '(rd, brd) := sp in
          let '(slog, blog, w, evs, tvs, ok, u) := runp g t rd brd 0 0 [] in
          if valid (fst (fst m)) slog && bvalid (snd (fst m)) blog
          then
            let '(m1, r) :=
              finish (fst (fst m)) (snd (fst m)) (snd m) fee g p
                     w evs tvs ok u in
            let '(m2, rs, n) := omerge m1 rest sps in
            (m2, r :: rs, n)
          else
            let '(m1, r) := step m i in
            let '(m2, rs, n) := omerge m1 rest sps in
            (m2, r :: rs, S n)
      | [] =>
          let '(m1, r) := step m i in
          let '(m2, rs, n) := omerge m1 rest [] in
          (m2, r :: rs, S n)
      end
  end.

Fixpoint prefix_specs (m : mach) (ts : list item) : list spec :=
  match ts with
  | [] => []
  | i :: rest =>
      (of_state (fst (fst m)), of_bank (snd (fst m)))
        :: prefix_specs (fst (step m i)) rest
  end.

(** ** The operational scheduler *)

Fixpoint dgo (ts0 : list item) (m : mach) (ord : list nat)
             (seen : list (nat * (storage * bank))) : list (nat * (storage * bank)) :=
  match ord with
  | [] => seen
  | p :: ps =>
      if existsb (fun pr => Nat.eqb (fst pr) p) seen
      then dgo ts0 m ps seen
      else
        match nth_error ts0 p with
        | None => dgo ts0 m ps seen
        | Some i => dgo ts0 (fst (step m i)) ps
                        ((p, (fst (fst m), snd (fst m))) :: seen)
        end
  end.

Definition dispatch (m0 : mach) (ts : list item) (order : list nat)
  : list spec :=
  let seen := dgo ts m0 order [] in
  map (fun j =>
         match find (fun pr => Nat.eqb (fst pr) j) seen with
         | Some pr => (of_state (fst (snd pr)), of_bank (snd (snd pr)))
         | None => (of_state (fst (fst m0)), of_bank (snd (fst m0)))
         end)
      (seq 0 (length ts)).

(** ** Gas soundness *)

Lemma pauper_rejected :
  forall st bk nm fee t g p,
    bk fee < g * p ->
    step (st, bk, nm) (fee, t, g, p) = ((st, bk, nm), (SRejected, 0, [], [], [])).
Proof.
  intros st bk nm fee t g p Hlt. unfold step.
  destruct (runp g t (of_state st) (of_bank bk) 0 0 [])
    as [[[[[[slog blog] w] evs] tvs] ok] u].
  unfold finish.
  destruct (Nat.leb (g * p) (bk fee)) eqn:Hle.
  - apply Nat.leb_le in Hle. lia.
  - reflexivity.
Qed.

(** ** Main theorem *)

Theorem optimistic_correct :
  forall ts specs m,
    fst (omerge m ts specs) = seq_execr m ts.
Proof.
  induction ts as [| i rest IH]; intros specs m.
  - reflexivity.
  - cbn [omerge seq_execr]. destruct specs as [| sp sps].
    + destruct (step m i) as [m1 r] eqn:Hstep.
      destruct (omerge m1 rest []) as [[m2 rs] n] eqn:E.
      assert (HI := IH [] m1). rewrite E in HI.
      rewrite <- HI. reflexivity.
    + destruct i as [[[fee t] g] p]. destruct m as [[st bk] nm].
      destruct sp as [srd sbrd].
      destruct (runp g t srd sbrd 0 0 [])
        as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
      cbn [fst snd].
      destruct (valid st slog && bvalid bk blog) eqn:Ev.
      * (* Validation passed: the speculative outcome commits as-is.  Replay
           shows this is exactly what sequential execution would have done. *)
        apply andb_true_iff in Ev. destruct Ev as [Evs Evb].
        assert (Hs : runp g t (of_state st) (of_bank bk) 0 0 []
                     = (slog, blog, w, evs, tvs, ok, u)).
        { exact (replay g t srd sbrd 0 0 st bk []
                        slog blog w evs tvs ok u Er
                        (valid_true_In slog st Evs)
                        (bvalid_true_In blog bk Evb) 0 0). }
        assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                        = finish st bk nm fee g p w evs tvs ok u).
        { cbn [step]. rewrite Hs. reflexivity. }
        rewrite Hstep.
        destruct (finish st bk nm fee g p w evs tvs ok u) as [m1 r].
        destruct (omerge m1 rest sps) as [[m2 rs] n] eqn:E.
        assert (HI := IH sps m1). rewrite E in HI.
        rewrite <- HI. reflexivity.
      * (* Validation failed: re-execute against the true prefix state. *)
        destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omerge m1 rest sps) as [[m2 rs] n] eqn:E.
        assert (HI := IH sps m1). rewrite E in HI.
        rewrite <- HI. reflexivity.
Qed.

(** ** Fast path *)

Theorem fast_path :
  forall ts m,
    omerge m ts (prefix_specs m ts) = (seq_execr m ts, 0).
Proof.
  induction ts as [| i rest IH]; intros m.
  - reflexivity.
  - cbn [omerge seq_execr prefix_specs]. destruct i as [[[fee t] g] p].
    destruct m as [[st bk] nm]. cbn [fst snd].
    destruct (runp g t (of_state st) (of_bank bk) 0 0 [])
      as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
    assert (Evs : valid st slog = true).
    { eapply valid_self_s. exact Er. }
    assert (Evb : bvalid bk blog = true).
    { eapply bvalid_self_b. exact Er. }
    rewrite Evs, Evb. cbn [andb].
    assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                    = finish st bk nm fee g p w evs tvs ok u).
    { cbn [step]. rewrite Er. reflexivity. }
    rewrite Hstep.
    destruct (finish st bk nm fee g p w evs tvs ok u) as [m1 r].
    cbn [fst].
    rewrite (IH m1).
    destruct (seq_execr m1 rest) as [m2 rs].
    reflexivity.
Qed.

(** ** Re-execution bound *)

Theorem reexec_bound :
  forall ts specs m,
    snd (omerge m ts specs) <= length ts.
Proof.
  induction ts as [| i rest IH]; intros specs m; cbn [omerge length snd].
  - lia.
  - destruct specs as [| sp sps].
    + destruct (step m i) as [m1 r].
      destruct (omerge m1 rest []) as [[m2 rs] n] eqn:E.
      assert (Hn := IH [] m1). rewrite E in Hn. simpl in Hn. simpl. lia.
    + destruct i as [[[fee t] g] p]. destruct m as [[st bk] nm].
      destruct sp as [srd sbrd].
      destruct (runp g t srd sbrd 0 0 [])
        as [[[[[[slog blog] w] evs] tvs] ok] u].
      cbn [fst snd].
      destruct (valid st slog && bvalid bk blog) eqn:Ev.
      * destruct (finish st bk nm fee g p w evs tvs ok u) as [m1 r].
        destruct (omerge m1 rest sps) as [[m2 rs] n] eqn:E.
        assert (Hn := IH sps m1). rewrite E in Hn. simpl in Hn. simpl. lia.
      * destruct (step (st, bk, nm) (fee, t, g, p)) as [m1 r].
        destruct (omerge m1 rest sps) as [[m2 rs] n] eqn:E.
        assert (Hn := IH sps m1). rewrite E in Hn. simpl in Hn. simpl. lia.
Qed.

(** ** Speculation independence *)

Corollary speculation_irrelevant :
  forall ts specs1 specs2 m,
    fst (omerge m ts specs1) = fst (omerge m ts specs2).
Proof.
  intros ts specs1 specs2 m.
  rewrite (optimistic_correct ts specs1 m).
  rewrite (optimistic_correct ts specs2 m).
  reflexivity.
Qed.

(** ** Scheduler correctness, all orders *)

Theorem scheduler_correct :
  forall ts order m,
    fst (omerge m ts (dispatch m ts order)) = seq_execr m ts.
Proof.
  intros ts order m. apply optimistic_correct.
Qed.

(** ** The in-order scheduler is perfect *)

Fixpoint mach_at (m : mach) (l : list item) (j : nat) : mach :=
  match j, l with
  | 0, _ => m
  | S _, [] => m
  | S j', i :: r => mach_at (fst (step m i)) r j'
  end.

Fixpoint snaps (d : nat) (m : mach) (l : list item)
  : list (nat * (storage * bank)) :=
  match l with
  | [] => []
  | i :: r => (d, (fst (fst m), snd (fst m))) :: snaps (S d) (fst (step m i)) r
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
    In (d + j, (fst (fst (mach_at m l j)), snd (fst (mach_at m l j))))
       (snaps d m l).
Proof.
  induction l as [| i r IH]; intros d m j Hj; simpl in Hj; [lia |].
  destruct j; simpl.
  - left. rewrite Nat.add_0_r. reflexivity.
  - right. rewrite Nat.add_succ_r.
    apply (IH (S d) (fst (step m i)) j). lia.
Qed.

Lemma existsb_key_false :
  forall (seen : list (nat * (storage * bank))) (p : nat),
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
  forall (l : list (nat * (storage * bank))) (j : nat) (v : storage * bank),
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
    nth j (prefix_specs m l) d
    = (of_state (fst (fst (mach_at m l j))), of_bank (snd (fst (mach_at m l j)))).
Proof.
  induction l as [| i r IH]; intros m j d Hj; simpl in Hj; [lia |].
  destruct j; simpl.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma dgo_inorder :
  forall (l ts0 : list item) (d : nat) (m : mach)
         (seen : list (nat * (storage * bank))),
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
                | Some pr => (of_state (fst (snd pr)), of_bank (snd (snd pr)))
                | None => (of_state (fst (fst m)), of_bank (snd (fst m)))
                end).
    apply nth_ext with (d := F 0)
                       (d' := (of_state (fst (fst m)), of_bank (snd (fst m)))).
    + rewrite length_map, length_seq. symmetry. apply prefix_specs_length.
    + intros j Hj. rewrite length_map, length_seq in Hj.
      rewrite map_nth.
      rewrite seq_nth by exact Hj.
      rewrite Nat.add_0_l.
      unfold F.
      rewrite (find_key_unique (rev (snaps 0 m ts)) j
                               (fst (fst (mach_at m ts j)),
                                snd (fst (mach_at m ts j)))).
      * cbn [fst snd]. symmetry. apply prefix_specs_nth. exact Hj.
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

(** ** Wavefront retry convergence

    A retrying scheduler finalizes a growing prefix: once the first [r]
    transactions speculate against their true prefix states, at most
    [length ts - r] re-executions remain, whatever the rest of the
    speculation is.  At [r = length ts] the merge is conflict-free: the
    retry loop converges in at most [length ts] rounds. *)

Theorem retry_progress :
  forall ts r m sps',
    snd (omerge m ts (firstn r (prefix_specs m ts) ++ sps'))
    <= length ts - r.
Proof.
  induction ts as [| i rest IH]; intros r m sps'.
  - cbn [omerge snd]. lia.
  - destruct r as [| r'].
    + cbn [firstn].
      etransitivity; [apply reexec_bound | lia].
    + cbn [prefix_specs firstn app].
      cbn [omerge]. destruct i as [[[fee t] g] p].
      destruct m as [[st bk] nm]. cbn [fst snd].
      destruct (runp g t (of_state st) (of_bank bk) 0 0 [])
        as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
      assert (Evs : valid st slog = true).
      { eapply valid_self_s. exact Er. }
      assert (Evb : bvalid bk blog = true).
      { eapply bvalid_self_b. exact Er. }
      rewrite Evs, Evb. cbn [andb].
      assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                      = finish st bk nm fee g p w evs tvs ok u).
      { cbn [step]. rewrite Er. reflexivity. }
      rewrite Hstep.
      destruct (finish st bk nm fee g p w evs tvs ok u) as [m1 r].
      cbn [fst].
      destruct (omerge m1 rest (firstn r' (prefix_specs m1 rest) ++ sps'))
        as [[m2 rs] n] eqn:E.
      assert (Hn := IH r' m1 sps'). rewrite E in Hn. simpl in Hn.
      simpl. lia.
Qed.

Corollary retry_converges :
  forall ts m sps',
    snd (omerge m ts (firstn (length ts) (prefix_specs m ts) ++ sps')) = 0.
Proof.
  intros ts m sps'.
  assert (H := retry_progress ts (length ts) m sps').
  lia.
Qed.

(** ** Work accounting

    Each transaction runs once speculatively plus once per re-execution, so
    total executions are the block length plus the re-execution count:
    never less than sequential, never more than twice it, and exactly
    sequential for in-order scheduling and for conflict-free blocks. *)

Definition executions (m : mach) (ts : list item) (specs : list spec)
  : nat := length ts + snd (omerge m ts specs).

Theorem work_bound :
  forall ts specs m,
    length ts <= executions m ts specs <= 2 * length ts.
Proof.
  intros ts specs m. unfold executions.
  assert (H := reexec_bound ts specs m). lia.
Qed.

Theorem work_inorder :
  forall ts m,
    executions m ts (dispatch m ts (seq 0 (length ts))) = length ts.
Proof.
  intros ts m. unfold executions.
  rewrite scheduler_in_order_optimal. simpl. lia.
Qed.

(** ** Money conservation

    The bank is an exact ledger across gas, coinbase, and transfers: for
    every account, final balance plus debits equals initial balance plus
    credits, where debits are the gas paid and transfers sent by
    transactions the account sponsored, and credits are coinbase gas income
    and transfers received. *)

Fixpoint debits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (fee, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb fee f then u * p + outsum tvs else 0) + debits f ts' rs'
  | _, _ => 0
  end.

Fixpoint credits (f : addr) (ts : list item) (rs : list rcpt) : nat :=
  match ts, rs with
  | (_, _, _, p) :: ts', (_, u, _, _, tvs) :: rs' =>
      (if Nat.eqb CB f then u * p else 0) + insum f tvs
      + credits f ts' rs'
  | _, _ => 0
  end.

Theorem money_conservation :
  forall ts m f,
    snd (fst (fst (seq_execr m ts))) f
    + debits f ts (snd (seq_execr m ts))
    = snd (fst m) f + credits f ts (snd (seq_execr m ts)).
Proof.
  induction ts as [| i rest IH]; intros m f.
  - cbn. lia.
  - cbn [seq_execr]. destruct i as [[[fee t] g] p].
    destruct m as [[st bk] nm].
    destruct (runp g t (of_state st) (of_bank bk) 0 0 [])
      as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
    assert (Hu : u <= g) by (eapply runp_gas_bound; exact Er).
    assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                    = finish st bk nm fee g p w evs tvs ok u).
    { cbn [step]. rewrite Er. reflexivity. }
    rewrite Hstep. unfold finish.
    destruct (Nat.leb (g * p) (bk fee)) eqn:Hle.
    + apply Nat.leb_le in Hle.
      assert (Hup : u * p <= bk fee).
      { eapply Nat.le_trans; [| exact Hle].
        apply Nat.mul_le_mono_r. exact Hu. }
      set (bk1 := bupd bk fee (bk fee - u * p)).
      set (bk2 := bupd bk1 CB (bk1 CB + u * p)).
      set (nm' := bupd nm fee (S (nm fee))).
      (* Gas leg: for every account, bk2 f + gas-debit = bk f + gas-credit. *)
      assert (Hgas : bk2 f + (if Nat.eqb fee f then u * p else 0)
                     = bk f + (if Nat.eqb CB f then u * p else 0)).
      { destruct (Nat.eqb fee f) eqn:Hff; destruct (Nat.eqb CB f) eqn:Hcb;
          cbn beta iota.
        - apply Nat.eqb_eq in Hff. apply Nat.eqb_eq in Hcb. subst f.
          subst fee.
          unfold bk2. rewrite bupd_same.
          unfold bk1. rewrite bupd_same. lia.
        - apply Nat.eqb_eq in Hff. apply Nat.eqb_neq in Hcb. subst fee.
          unfold bk2.
          rewrite (bupd_other bk1 CB (bk1 CB + u * p) f) by congruence.
          unfold bk1. rewrite bupd_same. lia.
        - apply Nat.eqb_neq in Hff. apply Nat.eqb_eq in Hcb. subst f.
          unfold bk2. rewrite bupd_same.
          unfold bk1.
          rewrite (bupd_other bk fee (bk fee - u * p) CB) by congruence.
          lia.
        - apply Nat.eqb_neq in Hff. apply Nat.eqb_neq in Hcb.
          unfold bk2.
          rewrite (bupd_other bk1 CB (bk1 CB + u * p) f) by congruence.
          unfold bk1.
          rewrite (bupd_other bk fee (bk fee - u * p) f) by congruence.
          lia. }
      destruct ok.
      * destruct (settle bk2 fee (rev tvs)) as [bk3 |] eqn:Hset.
        -- destruct (seq_execr (commit st w, bk3, nm') rest)
             as [m2 rs] eqn:E2.
           cbn [fst snd debits credits].
           assert (HI := IH (commit st w, bk3, nm') f).
           rewrite E2 in HI. cbn [fst snd] in HI.
           assert (HS := settle_law (rev tvs) bk2 fee bk3 Hset f).
           destruct (Nat.eqb fee f) eqn:Hff;
             destruct (Nat.eqb CB f) eqn:Hcb;
             try rewrite Hff in HS; try rewrite Hff in Hgas;
             try rewrite Hcb in Hgas;
             cbn beta iota in HS, Hgas; cbn beta iota; lia.
        -- destruct (seq_execr (st, bk2, nm') rest) as [m2 rs] eqn:E2.
           cbn [fst snd debits credits outsum insum].
           assert (HI := IH (st, bk2, nm') f).
           rewrite E2 in HI. cbn [fst snd] in HI.
           destruct (Nat.eqb fee f) eqn:Hff;
             destruct (Nat.eqb CB f) eqn:Hcb;
             try rewrite Hff in Hgas; try rewrite Hcb in Hgas;
             cbn beta iota in Hgas; cbn beta iota; lia.
      * destruct (seq_execr (st, bk2, nm') rest) as [m2 rs] eqn:E2.
        cbn [fst snd debits credits outsum insum].
        assert (HI := IH (st, bk2, nm') f).
        rewrite E2 in HI. cbn [fst snd] in HI.
        destruct (Nat.eqb fee f) eqn:Hff;
          destruct (Nat.eqb CB f) eqn:Hcb;
          try rewrite Hff in Hgas; try rewrite Hcb in Hgas;
          cbn beta iota in Hgas; cbn beta iota; lia.
    + destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      cbn [fst snd debits credits outsum insum].
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
      rewrite Nat.mul_0_l.
      destruct (Nat.eqb fee f) eqn:Hff;
        destruct (Nat.eqb CB f) eqn:Hcb;
        cbn beta iota; lia.
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
  - cbn [seq_execr]. destruct i as [[[fee t] g] p].
    destruct m as [[st bk] nm].
    destruct (runp g t (of_state st) (of_bank bk) 0 0 [])
      as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
    assert (Hstep : step (st, bk, nm) (fee, t, g, p)
                    = finish st bk nm fee g p w evs tvs ok u).
    { cbn [step]. rewrite Er. reflexivity. }
    rewrite Hstep. unfold finish.
    destruct (Nat.leb (g * p) (bk fee)) eqn:Hle.
    + set (bk1 := bupd bk fee (bk fee - u * p)).
      set (bk2 := bupd bk1 CB (bk1 CB + u * p)).
      set (nm' := bupd nm fee (S (nm fee))).
      assert (Hnm : forall f0, nm' f0
                    = nm f0 + (if Nat.eqb fee f0 then 1 else 0)).
      { intros f0. unfold nm'. destruct (Nat.eqb fee f0) eqn:Hf0.
        - apply Nat.eqb_eq in Hf0. subst f0. rewrite bupd_same. lia.
        - apply Nat.eqb_neq in Hf0.
          rewrite (bupd_other nm fee (S (nm fee)) f0) by congruence. lia. }
      destruct ok.
      * destruct (settle bk2 fee (rev tvs)) as [bk3 |] eqn:Hset.
        -- destruct (seq_execr (commit st w, bk3, nm') rest)
             as [m2 rs] eqn:E2.
           cbn [fst snd execd].
           assert (HI := IH (commit st w, bk3, nm') f).
           rewrite E2 in HI. cbn [fst snd] in HI.
           rewrite (Hnm f) in HI.
           destruct (Nat.eqb fee f) eqn:Hff;
             try rewrite Hff in HI; cbn beta iota in HI; cbn beta iota; lia.
        -- destruct (seq_execr (st, bk2, nm') rest) as [m2 rs] eqn:E2.
           cbn [fst snd execd].
           assert (HI := IH (st, bk2, nm') f).
           rewrite E2 in HI. cbn [fst snd] in HI.
           rewrite (Hnm f) in HI.
           destruct (Nat.eqb fee f) eqn:Hff;
             try rewrite Hff in HI; cbn beta iota in HI; cbn beta iota; lia.
      * destruct (seq_execr (st, bk2, nm') rest) as [m2 rs] eqn:E2.
        cbn [fst snd execd].
        assert (HI := IH (st, bk2, nm') f).
        rewrite E2 in HI. cbn [fst snd] in HI.
        rewrite (Hnm f) in HI.
        destruct (Nat.eqb fee f) eqn:Hff;
          try rewrite Hff in HI; cbn beta iota in HI; cbn beta iota; lia.
    + destruct (seq_execr (st, bk, nm) rest) as [m2 rs] eqn:E2.
      cbn [fst snd execd].
      assert (HI := IH (st, bk, nm) f).
      rewrite E2 in HI. cbn [fst snd] in HI.
      destruct (Nat.eqb fee f) eqn:Hff; cbn beta iota; lia.
Qed.

(** ** Conflict-free blocks merge without re-execution

    Conflict freedom concerns storage footprints; the hypothesis
    [bank_reads] excludes balance reads, since the bank moves at every
    commit through gas. *)

Definition disjoint (xs ys : list addr) : Prop :=
  forall a, In a xs -> In a ys -> False.

Definition reads_of (st : storage) (B : breader) (i : item) : list addr :=
  let '(fee, t, g, p) := i in
  map fst (o_log (runp g t (of_state st) B 0 0 [])).

Definition writes_of (st : storage) (B : breader) (i : item) : list addr :=
  let '(fee, t, g, p) := i in
  map fst (o_buf (runp g t (of_state st) B 0 0 [])).

Definition bank_reads (st : storage) (B : breader) (i : item)
  : list (addr * nat) :=
  let '(fee, t, g, p) := i in
  o_blog (runp g t (of_state st) B 0 0 []).

Lemma disjoint_go :
  forall ts (st0 stp : storage) (B : breader) (bk : bank) (nm : nonces)
         (W : list addr),
    (forall a, ~ In a W -> stp a = st0 a) ->
    (forall i, In i ts -> bank_reads st0 B i = []) ->
    (forall i, In i ts -> disjoint W (reads_of st0 B i)) ->
    (forall j k ij ik,
        j < k ->
        nth_error ts j = Some ij ->
        nth_error ts k = Some ik ->
        disjoint (writes_of st0 B ij) (reads_of st0 B ik)) ->
    snd (omerge (stp, bk, nm) ts
                (@map item spec (fun _ => (of_state st0, B)) ts)) = 0.
Proof.
  induction ts as [| i rest IH]; intros st0 stp B bk nm W Hag Hbr H2 H3.
  - reflexivity.
  - cbn [omerge map]. destruct i as [[[fee t] g] p].
    destruct (runp g t (of_state st0) B 0 0 [])
      as [[[[[[slog blog] w] evs] tvs] ok] u] eqn:Er.
    cbn [fst snd].
    assert (Hrd : reads_of st0 B (fee, t, g, p) = map fst slog).
    { unfold reads_of, o_log. rewrite Er. reflexivity. }
    assert (Hwr : writes_of st0 B (fee, t, g, p) = map fst w).
    { unfold writes_of, o_buf. rewrite Er. reflexivity. }
    assert (Hblog : blog = []).
    { specialize (Hbr (fee, t, g, p) (or_introl eq_refl)).
      unfold bank_reads in Hbr. rewrite Er in Hbr.
      cbn [o_blog] in Hbr. exact Hbr. }
    subst blog.
    assert (Ev : valid stp slog = true).
    { eapply valid_stable.
      - eapply valid_self_s. exact Er.
      - intros a Hin. apply Hag.
        intro HW.
        apply (H2 (fee, t, g, p) (or_introl eq_refl) a HW).
        rewrite Hrd. exact Hin. }
    cbn [bvalid]. rewrite andb_true_r. rewrite Ev.
    assert (Hag' : forall stp',
               (forall a, ~ In a (map fst w) -> stp' a = stp a) ->
               forall a, ~ In a (writes_of st0 B (fee, t, g, p) ++ W) ->
               stp' a = st0 a).
    { intros stp' Hloc a Hnin.
      rewrite Hwr in Hnin.
      assert (Hnw : ~ In a (map fst w)).
      { intro Hx. apply Hnin. apply in_or_app. left. exact Hx. }
      assert (HnW : ~ In a W).
      { intro Hx. apply Hnin. apply in_or_app. right. exact Hx. }
      rewrite (Hloc a Hnw). apply Hag. exact HnW. }
    assert (Hbr' : forall i', In i' rest -> bank_reads st0 B i' = []).
    { intros i' Hin. apply Hbr. right. exact Hin. }
    assert (H2' : forall i', In i' rest ->
               disjoint (writes_of st0 B (fee, t, g, p) ++ W)
                        (reads_of st0 B i')).
    { intros i' Hin a Ha Hr.
      apply in_app_or in Ha. destruct Ha as [Ha | Ha].
      - apply In_nth_error in Hin. destruct Hin as [k Hk].
        exact (H3 0 (S k) (fee, t, g, p) i'
                  (Nat.lt_0_succ k) eq_refl Hk a Ha Hr).
      - exact (H2 i' (or_intror Hin) a Ha Hr). }
    assert (H3' : forall j k ij ik,
               j < k ->
               nth_error rest j = Some ij ->
               nth_error rest k = Some ik ->
               disjoint (writes_of st0 B ij) (reads_of st0 B ik)).
    { intros j k ij ik Hjk Hj Hk.
      apply (H3 (S j) (S k) ij ik); [lia | exact Hj | exact Hk]. }
    unfold finish.
    destruct (Nat.leb (g * p) (bk fee)) eqn:Hgle.
    + destruct ok eqn:Hok.
      * destruct (settle (bupd (bupd bk fee (bk fee - u * p)) CB
                               (bupd bk fee (bk fee - u * p) CB + u * p))
                         fee (rev tvs)) as [bk3 |] eqn:Hset.
        -- destruct (omerge (commit stp w, bk3,
                             bupd nm fee (S (nm fee))) rest
                            (@map item spec (fun _ => (of_state st0, B)) rest))
             as [[m2 rs] n] eqn:E.
           assert (Hn := IH st0 (commit stp w) B bk3
                            (bupd nm fee (S (nm fee)))
                            (writes_of st0 B (fee, t, g, p) ++ W)
                            (Hag' (commit stp w)
                                  (fun a Hna =>
                                     commit_untouched w stp a Hna))
                            Hbr' H2' H3').
           rewrite E in Hn. simpl in Hn. simpl. exact Hn.
        -- destruct (omerge (stp,
                             bupd (bupd bk fee (bk fee - u * p)) CB
                                  (bupd bk fee (bk fee - u * p) CB + u * p),
                             bupd nm fee (S (nm fee))) rest
                            (@map item spec (fun _ => (of_state st0, B)) rest))
             as [[m2 rs] n] eqn:E.
           assert (Hn := IH st0 stp B
                            (bupd (bupd bk fee (bk fee - u * p)) CB
                                  (bupd bk fee (bk fee - u * p) CB + u * p))
                            (bupd nm fee (S (nm fee)))
                            (writes_of st0 B (fee, t, g, p) ++ W)
                            (Hag' stp (fun a _ => eq_refl))
                            Hbr' H2' H3').
           rewrite E in Hn. simpl in Hn. simpl. exact Hn.
      * destruct (omerge (stp,
                          bupd (bupd bk fee (bk fee - u * p)) CB
                               (bupd bk fee (bk fee - u * p) CB + u * p),
                          bupd nm fee (S (nm fee))) rest
                         (@map item spec (fun _ => (of_state st0, B)) rest))
          as [[m2 rs] n] eqn:E.
        assert (Hn := IH st0 stp B
                         (bupd (bupd bk fee (bk fee - u * p)) CB
                               (bupd bk fee (bk fee - u * p) CB + u * p))
                         (bupd nm fee (S (nm fee)))
                         (writes_of st0 B (fee, t, g, p) ++ W)
                         (Hag' stp (fun a _ => eq_refl))
                         Hbr' H2' H3').
        rewrite E in Hn. simpl in Hn. simpl. exact Hn.
    + destruct (omerge (stp, bk, nm) rest
                       (@map item spec (fun _ => (of_state st0, B)) rest))
        as [[m2 rs] n] eqn:E.
      assert (Hn := IH st0 stp B bk nm
                       (writes_of st0 B (fee, t, g, p) ++ W)
                       (Hag' stp (fun a _ => eq_refl))
                       Hbr' H2' H3').
      rewrite E in Hn. simpl in Hn. simpl. exact Hn.
Qed.

Theorem disjoint_block_free :
  forall ts (st : storage) (bk : bank) (nm : nonces),
    (forall i, In i ts -> bank_reads st (of_bank bk) i = []) ->
    (forall j k ij ik,
        j < k ->
        nth_error ts j = Some ij ->
        nth_error ts k = Some ik ->
        disjoint (writes_of st (of_bank bk) ij) (reads_of st (of_bank bk) ik)) ->
    snd (omerge (st, bk, nm) ts
                (@map item spec (fun _ => (of_state st, of_bank bk)) ts)) = 0.
Proof.
  intros ts st bk nm Hbr H3.
  apply (disjoint_go ts st st (of_bank bk) bk nm []).
  - intros a _. reflexivity.
  - exact Hbr.
  - intros i _ a Ha. contradiction.
  - exact H3.
Qed.

Theorem work_disjoint :
  forall ts (st : storage) (bk : bank) (nm : nonces),
    (forall i, In i ts -> bank_reads st (of_bank bk) i = []) ->
    (forall j k ij ik,
        j < k ->
        nth_error ts j = Some ij ->
        nth_error ts k = Some ik ->
        disjoint (writes_of st (of_bank bk) ij) (reads_of st (of_bank bk) ik)) ->
    executions (st, bk, nm) ts
               (@map item spec (fun _ => (of_state st, of_bank bk)) ts)
    = length ts.
Proof.
  intros ts st bk nm Hbr H3. unfold executions.
  rewrite (disjoint_block_free ts st bk nm Hbr H3). lia.
Qed.

End WithCoinbase.

(** ** Executable examples

    Coinbase is account 7; fees come from account 9, funded with 100;
    storage starts at zero; gas price 1. *)

Definition CBX : addr := 7.
Definition FEE : addr := 9.
Definition tA : tx := TWrite 0 1 TDone.
Definition tB : tx := TRead 0 (fun v => TWrite 1 v TDone).
Definition st0 : storage := fun _ => 0.
Definition bk0 : bank := fun a => if Nat.eqb a FEE then 100 else 0.
Definition nm0 : nonces := fun _ => 0.
Definition m0 : mach := (st0, bk0, nm0).
Definition sp0 : spec := (of_state st0, of_bank bk0).
Definition block : list item := [(FEE, tA, 2, 1); (FEE, tB, 2, 1)].

Example conflict_detected :
  snd (omerge CBX m0 block [sp0; sp0]) = 1.
Proof. reflexivity. Qed.

Example conflict_result_correct :
  fst (fst (fst (fst (omerge CBX m0 block [sp0; sp0])))) 1
  = 1.
Proof. reflexivity. Qed.

(** Fees moved exactly: three units left account 9 and arrived at the
    coinbase. *)

Example conflict_fees_exact :
  let bkf := snd (fst (fst (fst (omerge CBX m0 block [sp0; sp0])))) in
  (bkf FEE, bkf CBX) = (97, 3).
Proof. reflexivity. Qed.

Example torn_view_detected :
  snd (omerge CBX m0 block [sp0; ((fun _ _ => 999), of_bank bk0)]) = 1.
Proof. reflexivity. Qed.

Example perfect_speculation_free :
  snd (omerge CBX m0 block (prefix_specs CBX m0 block)) = 0.
Proof. reflexivity. Qed.

Example scheduler_in_order_free :
  snd (omerge CBX m0 block (dispatch CBX m0 block [0; 1])) = 0.
Proof. reflexivity. Qed.

Example scheduler_out_of_order_detected :
  snd (omerge CBX m0 block (dispatch CBX m0 block [1; 0])) = 1.
Proof. reflexivity. Qed.

(** A stale balance read is a conflict: transaction 1 pays gas, so a
    speculative read of the fee balance against the initial bank disagrees
    at merge time; the transaction is re-executed and stores the true
    balance. *)

Definition tBalW : tx := TBal FEE (fun b => TWrite 2 b TDone).

Example stale_balance_detected :
  snd (omerge CBX m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)] [sp0; sp0]) = 1.
Proof. reflexivity. Qed.

Example stale_balance_corrected :
  fst (fst (fst (fst (omerge CBX m0
      [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)] [sp0; sp0])))) 2 = 99.
Proof. reflexivity. Qed.

(** Balance speculation against the true prefix bank validates. *)

Example balance_prefix_free :
  snd (omerge CBX m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)]
       (prefix_specs CBX m0 [(FEE, tA, 2, 1); (FEE, tBalW, 2, 1)])) = 0.
Proof. reflexivity. Qed.

(** Transfers settle and land: account 9 pays 30 to account 5, plus 1 gas. *)

Example transfer_settles :
  let res := omerge CBX m0 [(FEE, TPay 5 30 TDone, 1, 1)] [sp0] in
  let bkf := snd (fst (fst (fst res))) in
  (bkf FEE, bkf 5, bkf CBX) = (69, 30, 1).
Proof. reflexivity. Qed.

(** An insufficient transfer reverts the transaction: the gas is still paid
    and nothing else moves. *)

Example transfer_insufficient_reverts :
  let res := omerge CBX m0 [(FEE, TPay 5 500 TDone, 1, 1)] [sp0] in
  let bkf := snd (fst (fst (fst res))) in
  (bkf FEE, bkf 5, snd (fst res)) = (99, 0, [(SRev, 1, [], [], [])]).
Proof. reflexivity. Qed.

(** Events appear in the receipt of a completing transaction and are
    discarded by a revert. *)

Example event_emitted :
  snd (fst (omerge CBX m0 [(FEE, TEmit 42 TDone, 1, 1)] [sp0]))
  = [(SOk, 1, [], [42], [])].
Proof. reflexivity. Qed.

Example event_discarded_on_revert :
  snd (fst (omerge CBX m0 [(FEE, TEmit 42 TRevert, 1, 1)] [sp0]))
  = [(SRev, 1, [], [], [])].
Proof. reflexivity. Qed.

(** Nonces advance for executed and reverted transactions, not rejected
    ones. *)

Example nonce_bumps :
  let res := omerge CBX m0 block [sp0; sp0] in
  (nm0 FEE, snd (fst (fst res)) FEE) = (0, 2).
Proof. reflexivity. Qed.

Example pauper_pays_nothing :
  omerge CBX m0 [(FEE, TWrite 0 5 TDone, 200, 1)] [sp0]
  = ((m0, [(SRejected, 0, [], [], [])]), 0).
Proof. reflexivity. Qed.

(** Writing the fee address in storage buys nothing: banks are typed apart
    from storage. *)

Example counterfeit_impossible :
  let res := omerge CBX m0 [(FEE, TWrite FEE 777 TDone, 2, 1)] [sp0] in
  (fst (fst (fst (fst res))) FEE, snd (fst (fst (fst res))) FEE)
  = (777, 99).
Proof. reflexivity. Qed.

Definition disjoint_pair : list item :=
  [(FEE, tA, 2, 1); (FEE, TWrite 3 7 TDone, 2, 1)].

Example disjoint_validates :
  snd (omerge CBX m0 disjoint_pair [sp0; sp0]) = 0.
Proof. reflexivity. Qed.

Definition countdown : tx :=
  TWrite 0 3 (TWhile 0 (TRead 0 (fun v => TWrite 0 (pred v) TDone)) TDone).

Example loop_terminates_exactly :
  let res := omerge CBX m0 [(FEE, countdown, 11, 1)] [sp0] in
  (fst (fst (fst (fst res))) 0, snd (fst (fst (fst res))) FEE) = (0, 89).
Proof. reflexivity. Qed.

Definition spin : tx := TWrite 0 1 (TWhile 0 TDone TDone).

Example spin_reverts_charged :
  let res := omerge CBX m0 [(FEE, spin, 5, 1)] [sp0] in
  (fst (fst (fst (fst res))) 0, snd (fst (fst (fst res))) FEE,
   snd (fst res))
  = (0, 95, [(SRev, 5, [], [], [])]).
Proof. reflexivity. Qed.

(** All results are closed under the global context. *)

Print Assumptions optimistic_correct.
Print Assumptions fast_path.
Print Assumptions dispatch_in_order.
Print Assumptions scheduler_in_order_optimal.
Print Assumptions scheduler_correct.
Print Assumptions reexec_bound.
Print Assumptions speculation_irrelevant.
Print Assumptions retry_progress.
Print Assumptions retry_converges.
Print Assumptions work_bound.
Print Assumptions work_inorder.
Print Assumptions work_disjoint.
Print Assumptions money_conservation.
Print Assumptions omerge_money_conservation.
Print Assumptions nonce_law.
Print Assumptions disjoint_block_free.
Print Assumptions runp_gas_bound.
Print Assumptions pauper_rejected.
Print Assumptions settle_law.
