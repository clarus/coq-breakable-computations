(** Experiments on encoding concurrency in Coq. *)
Require Import Coq.Lists.List.
Require Import Coq.Lists.Streams.

Import ListNotations.

(** Definition of a computation. *)
Module C.
  Inductive t (S E A : Type) : Type :=
  | Value : A -> t S E A
  | Error : E -> t S E A
  | Break : (S -> t S E A) -> (S -> S) -> t S E A.
  Arguments Value {S E A} _.
  Arguments Error {S E A} _.
  Arguments Break {S E A} _ _.
End C.

Module Eq.
  Inductive t {S E A} : C.t S E A -> C.t S E A -> Prop :=
  | Value : forall (v : A), t (C.Value v) (C.Value v)
  | Error : forall (e : E), t (C.Error e) (C.Error e)
  | Break : forall xs1 xs2 ss1 ss2,
    (forall s, t (xs1 s) (xs2 s)) -> (forall s, ss1 s = ss2 s) ->
    t (C.Break xs1 ss1) (C.Break xs2 ss2).

  Fixpoint reflexivity {S E A} {x : C.t S E A} : t x x.
    destruct x as [v | e | xs ss]; now constructor.
  Qed.

  Fixpoint symmetry {S E A} {x1 x2 : C.t S E A} (H : t x1 x2) : t x2 x1.
    destruct H; constructor.
    - intro s; now apply symmetry.
    - intro s; now symmetry.
  Qed.

  Fixpoint transitivity {S E A} {x1 x2 x3 : C.t S E A}
    (H12 : t x1 x2) (H23 : t x2 x3) : t x1 x3.
    destruct H12; try apply H23.
    inversion H23.
    apply Break; intro s.
    - now apply (transitivity _ _ _ _ _ _  (H s)).
    - congruence.
  Qed.
End Eq.

(** Monadic return. *)
Definition ret {S E A} (v : A) : C.t S E A :=
  C.Value v.

(** Monadic bind. *)
Fixpoint bind {S E A B} (x : C.t S E A) (f : A -> C.t S E B) : C.t S E B :=
  match x with
  | C.Value v => f v
  | C.Error e => C.Error e
  | C.Break xs ss => C.Break (fun s => bind (xs s) f) ss
  end.

Module Notations.
  Notation "'let!' x ':=' A 'in' B" := (bind A (fun x => B))
    (at level 200, x ident, A at level 100, B at level 200).

  Notation "'let!' x : T ':=' A 'in' B" := (bind A (fun (x : T) => B))
    (at level 200, x ident, A at level 100, T at level 200, B at level 200).

  Notation "'do!' A 'in' B" := (bind A (fun (_ : unit) => B))
    (at level 200, A at level 100, B at level 200).
End Notations.

Module MonadicLaw.
  Definition neutral_left {S E A B} (x : A) (f : A -> C.t S E B)
    : Eq.t (bind (ret x) f) (f x).
    apply Eq.reflexivity.
  Qed.

  Fixpoint neutral_right {S E A} (x : C.t S E A)
    : Eq.t (bind x ret) x.
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s.
    - apply neutral_right.
    - reflexivity.
  Qed.

  Fixpoint associativity {S E A B C}
    (x : C.t S E A) (f : A -> C.t S E B) (g : B -> C.t S E C) {struct x}
    : Eq.t (bind (bind x f) g) (bind x (fun x => bind (f x) g)).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s.
    - apply associativity.
    - reflexivity.
  Qed.
End MonadicLaw.

(** Sequential monad. *)
Module M.
  Definition t (S E A : Type) : Type :=
    S -> (A + E) * S.

  Definition ret {S E A} (v : A) : t S E A :=
    fun s => (inl v, s).

  Definition bind {S E A B} (x : t S E A) (f : A -> t S E B) : t S E B :=
    fun s =>
      let (r, s) := x s in
      match r with
      | inl v => f v s
      | inr e => (inr e, s)
      end.

  Module Eq.
    Definition t {S E A} (x1 x2 : t S E A) : Prop :=
      forall s, x1 s = x2 s.

    Definition reflexivity {S E A} {x : M.t S E A} : t x x.
      intro s; reflexivity.
    Qed.

    Definition symmetry {S E A} {x1 x2 : M.t S E A} (H : t x1 x2) : t x2 x1.
      intro s; now symmetry.
    Qed.

    Definition transitivity {S E A} {x1 x2 x3 : M.t S E A}
      (H12 : t x1 x2) (H23 : t x2 x3) : t x1 x3.
      intro s; now rewrite H12.
    Qed.
  End Eq.
End M.

(** Raw evaluation. *)
Fixpoint eval {S E A} (x : C.t S E A) : M.t S E A :=
  fun s =>
    match x with
    | C.Value v => (inl v, s)
    | C.Error e => (inr e, s)
    | C.Break xs ss => eval (xs s) (ss s)
    end.

Module EvalProperties.
  Definition ret {S E A} {v : A}
    : M.Eq.t (S := S) (E := E) (eval (ret v)) (M.ret v).
    apply M.Eq.reflexivity.
  Qed.

  Fixpoint bind {S E A B} (x : C.t S E A) (f : A -> C.t S E B) {struct x}
    : M.Eq.t (eval (bind x f)) (M.bind (eval x) (fun v => eval (f v))).
    destruct x as [v | e | xs ss]; unfold M.bind; simpl;
      try apply M.Eq.reflexivity.
    intro s; now rewrite bind.
  Qed.

  Fixpoint eq {S E A} {x1 x2 : C.t S E A} (H : Eq.t x1 x2)
    : M.Eq.t (eval x1) (eval x2).
    destruct H; simpl; try apply M.Eq.reflexivity.
    intro s.
    replace (ss2 s) with (ss1 s); trivial.
    now apply eq.
  Qed.
End EvalProperties.

(** Augment the state. *)
Fixpoint lift_state {S1 S2 E A} (x : C.t S1 E A) : C.t (S1 * S2) E A :=
  match x with
  | C.Value v => C.Value v
  | C.Error e => C.Error e
  | C.Break xs ss =>
    C.Break (fun s => lift_state (xs (fst s))) (fun s => (ss (fst s), snd s))
  end.

(** Augment the error. *)
Fixpoint lift_error {S E1 E2 A} (x : C.t S E1 A) : C.t S (E1 + E2) A :=
  match x with
  | C.Value v => C.Value v
  | C.Error e => C.Error (inl e)
  | C.Break xs ss => C.Break (fun s => lift_error (xs s)) ss
  end.

Module LiftProperties.
  Definition state_ret {S1 S2 E A} {v : A}
    : Eq.t (S := S1 * S2) (E := E) (lift_state (ret v)) (ret v).
    apply Eq.reflexivity.
  Qed.

  Fixpoint state_bind {S1 S2 E A B} (x : C.t S1 E A) (f : A -> C.t S1 E B)
    {struct x}
    : Eq.t (S := S1 * S2) (E := E)
      (lift_state (bind x f))
      (bind (lift_state x) (fun v => lift_state (f v))).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity; destruct s as [s1 s2]; simpl.
    apply state_bind.
  Qed.

  Definition error_ret {S E1 E2 A} {v : A}
    : Eq.t (S := S) (E := E1 + E2) (lift_error (ret v)) (ret v).
    apply Eq.reflexivity.
  Qed.

  Fixpoint error_bind {S E1 E2 A B} (x : C.t S E1 A) (f : A -> C.t S E1 B)
    {struct x}
    : Eq.t (S := S) (E := E1 + E2)
      (lift_error (bind x f))
      (bind (lift_error x) (fun v => lift_error (f v))).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity; apply error_bind.
  Qed.

  Fixpoint error_state {S1 S2 E1 E2 A} {x : C.t S1 E1 A}
    : Eq.t (S := S1 * S2) (E := E1 + E2)
      (lift_error (lift_state x)) (lift_state (lift_error x)).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity; apply error_state.
  Qed.
End LiftProperties.

(** Apply an isomorphism to the state. *)
Fixpoint map_state {S1 S2 E A} (f : S1 -> S2) (g : S2 -> S1) (x : C.t S1 E A)
  : C.t S2 E A :=
  match x with
  | C.Value v => C.Value v
  | C.Error e => C.Error e
  | C.Break xs ss =>
    C.Break (fun s2 => map_state f g (xs (g s2))) (fun s2 => f (ss (g s2)))
  end.

(** Apply an isomorphism to the error. *)
Fixpoint map_error {S E1 E2 A} (f : E1 -> E2) (g : E2 -> E1) (x : C.t S E1 A)
  : C.t S E2 A :=
  match x with
  | C.Value v => C.Value v
  | C.Error e => C.Error (f e)
  | C.Break xs ss => C.Break (fun s => map_error f g (xs s)) ss
  end.

Module MapProperties.
  Definition compose {A B C} (f : A -> B) (g : B -> C) : A -> C :=
    fun x => g (f x).

  Definition state_ret {S1 S2 E A} {f12 : S1 -> S2} {f21 : S2 -> S1} {v : A}
    : Eq.t (E := E) (map_state f12 f21 (ret v)) (ret v).
    apply Eq.reflexivity.
  Qed.

  Fixpoint state_bind {S1 S2 E A B} {f12 : S1 -> S2} {f21 : S2 -> S1}
    (x : C.t S1 E A) (f : A -> C.t S1 E B) {struct x}
    : Eq.t (E := E)
      (map_state f12 f21 (bind x f))
      (bind (map_state f12 f21 x) (fun v => map_state f12 f21 (f v))).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply state_bind.
  Qed.

  Fixpoint state_id {S E A} {x : C.t S E A}
    : Eq.t (map_state (fun s => s) (fun s => s) x) x.
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply state_id.
  Qed.

  Fixpoint state_compose {S1 S2 S3 E A} {f12 : S1 -> S2} {f21 : S2 -> S1}
    {f23 : S2 -> S3} {f32 : S3 -> S2} {x : C.t S1 E A}
    : Eq.t
      (map_state f23 f32 (map_state f12 f21 x))
      (map_state (compose f12 f23) (compose f32 f21) x).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply state_compose.
  Qed.

  Fixpoint state_rev {S1 S2 E A} {f12 : S1 -> S2} {f21 : S2 -> S1}
    (H : forall s1, f21 (f12 s1) = s1) {x : C.t S1 E A}
    : Eq.t (map_state f21 f12 (map_state f12 f21 x)) x.
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; repeat rewrite H.
    - now apply state_rev.
    - reflexivity.
  Qed.

  Definition error_ret {S E1 E2 A} {f12 : E1 -> E2} {f21 : E2 -> E1} {v : A}
    : Eq.t (S := S) (map_error f12 f21 (ret v)) (ret v).
    apply Eq.reflexivity.
  Qed.

  Fixpoint error_bind {S E1 E2 A B} {f12 : E1 -> E2} {f21 : E2 -> E1}
    (x : C.t S E1 A) (f : A -> C.t S E1 B) {struct x}
    : Eq.t (S := S)
      (map_error f12 f21 (bind x f))
      (bind (map_error f12 f21 x) (fun v => map_error f12 f21 (f v))).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply error_bind.
  Qed.

  Fixpoint error_id {S E A} {x : C.t S E A}
    : Eq.t (map_error (fun s => s) (fun s => s) x) x.
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply error_id.
  Qed.

  Fixpoint error_compose {S E1 E2 E3 A} {f12 : E1 -> E2} {f21 : E2 -> E1}
    {f23 : E2 -> E3} {f32 : E3 -> E2} {x : C.t S E1 A}
    : Eq.t
      (map_error f23 f32 (map_error f12 f21 x))
      (map_error (compose f12 f23) (compose f32 f21) x).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s; try reflexivity.
    apply error_compose.
  Qed.
End MapProperties.

Module Option.
  Definition none {S A} : C.t S unit A :=
    C.Error tt.

  Fixpoint handle {S E A} (x : C.t S (unit + E) A) : C.t S E (option A) :=
    match x with
    | C.Value v => C.Value (Some v)
    | C.Error (inl _) => C.Value None
    | C.Error (inr e) => C.Error e
    | C.Break xs ss => C.Break (fun s => handle (xs s)) ss
    end.
End Option.

Module Error.
  Definition raise {S E A} (e : E) : C.t S E A :=
    C.Error e.

  Fixpoint handle {S E1 E2 A} (x : C.t S (E1 + E2) A) : C.t S E2 (A + E1) :=
    match x with
    | C.Value v => C.Value (inl v)
    | C.Error (inl e1) => C.Value (inr e1)
    | C.Error (inr e2) => C.Error e2
    | C.Break xs ss => C.Break (fun s => handle (xs s)) ss
    end.
End Error.

Module State.
  Definition read {S E : Type} : C.t S E S :=
    C.Break (fun s => C.Value s) (fun s => s).

  Definition write {S E : Type} (s : S) : C.t S E unit :=
    C.Break (fun _ => C.Value tt) (fun _ => s).
End State.

Module NonTermination.
  Import Notations.

  Definition use_fuel {S E A B : Type} (f : A -> nat -> C.t S E (option B)) (x : A) : C.t (S * nat) (E + unit) B :=
    let! s_fuel : S * nat := State.read in
    let (s, fuel) := s_fuel in
    let! result := lift_error (lift_state (f x fuel)) in
    match result with
    | None => C.Error (inr tt)
    | Some y => ret y
    end.
End NonTermination.

Module Log.
  Definition t := list.

  Definition log {E A} (x : A) : C.t (t A) E unit :=
    C.Break (fun _ => C.Value tt) (fun s => x :: s).
End Log.

(** A source of information for a concurrent scheduler. *)
Module Entropy.
  Require Import BinNat.

  Definition t := Stream bool.

  Definition left : t := Streams.const true.

  Definition right : t := Streams.const false.

  Definition inverse (e : t) : t :=
    Streams.map negb e.

  Definition half : t :=
    let cofix aux b :=
      Streams.Cons b (aux (negb b)) in
    aux true.

  CoFixpoint random_naturals (n : N) : Stream N :=
    let n' := N.modulo (137 * n + 187) 256 in
    Streams.Cons n (random_naturals n').

  Definition random (seed : N) : t :=
    Streams.map (fun n => N.even (N.div n 64)) (random_naturals seed).

  Module Test.
    Fixpoint hds {A} (n : nat) (e : Stream A) : list A :=
      match n with
      | O => []
      | S n => Streams.hd e :: hds n (Streams.tl e)
      end.

    Definition test_1 : hds 20 (random_naturals 0) = [
      0; 187; 206; 249; 252; 151; 138; 149; 120; 243;
      198; 177; 116; 207; 130; 77; 240; 43; 190; 105] % N :=
      eq_refl.

    Definition test_2 : hds 20 (random 0) = [
      true; true; false; false; false; true; true; true; false; false;
      false; true; false; false; true; false; false; true; true; false] :=
      eq_refl.

    Definition test_3 : hds 20 (random 12) = [
      true; true; true; true; true; true; false; false; true; false; true;
      false; true; true; false; false; false; true; true; true] :=
      eq_refl.

    Definition test_4 : hds 20 (random 23) = [
      true; true; true; false; false; false; true; false; false; true;
      false; false; true; true; false; false; true; false; true; false] :=
      eq_refl.
  End Test.
End Entropy.

Module Concurrency.
  Import Notations.

  Definition choose {S E} : C.t (S * Entropy.t) E bool :=
    let! state := State.read in
    match state with
    | (s, Streams.Cons b bs) =>
      do! State.write (s, bs) in
      ret b
    end.

  Fixpoint par {S E A B}
    (x : C.t (S * Entropy.t) E A) (y : C.t (S * Entropy.t) E B) {struct x}
    : C.t (S * Entropy.t) E (A * B) :=
    let fix par_aux y {struct y} : C.t (S * Entropy.t) E (A * B) :=
      match x with
      | C.Value v_x => let! v_y := y in ret (v_x, v_y)
      | C.Error e_x =>
        match y with
        | C.Value _ | C.Break _ _ => C.Error e_x
        | C.Error e_y =>
          let! b := choose in
          if b then
            C.Error e_x
          else
            C.Error e_y
        end
      | C.Break xs sxs =>
        match y with
        | C.Value v_y => let! v_x := x in ret (v_x, v_y)
        | C.Error e_y => C.Error e_y
        | C.Break ys sys =>
          let! b := choose in
          if b then
            C.Break (fun s => par (xs s) y) sxs
          else
            C.Break (fun s => par_aux (ys s)) sys
        end
      end in
    match x with
    | C.Value v_x => let! v_y := y in ret (v_x, v_y)
    | C.Error e_x =>
      match y with
      | C.Value _ | C.Break _ _ => C.Error e_x
      | C.Error e_y =>
        let! b := choose in
        if b then
          C.Error e_x
        else
          C.Error e_y
      end
    | C.Break xs sxs =>
      match y with
      | C.Value v_y => let! v_x := x in ret (v_x, v_y)
      | C.Error e_y => C.Error e_y
      | C.Break ys sys =>
        let! b := choose in
        if b then
          C.Break (fun s => par (xs s) y) sxs
        else
          C.Break (fun s => par_aux (ys s)) sys
      end
    end.

  Definition par_unit {S E}
    (x : C.t (S * Entropy.t) E unit) (y : C.t (S * Entropy.t) E unit)
    : C.t (S * Entropy.t) E unit :=
    let! _ := par x y in
    ret tt.

  (** Make [x] atomic. *)
  Definition atomic {S E A} (x : C.t S E A) : C.t S E A :=
    match x with
    | C.Value _ | C.Error _ => x
    | C.Break _ _ =>
      C.Break
        (fun s =>
          match fst (eval x s) with
          | inl v => C.Value v
          | inr e => C.Error e
          end)
        (fun s => snd (eval x s))
    end.
End Concurrency.

Module List.
  Import Notations.

  Fixpoint iter_seq {S E A} (f : A -> C.t S E unit) (l : list A) : C.t S E unit :=
    match l with
    | [] => ret tt
    | x :: l =>
      let! _ := f x in
      iter_seq f l
    end.

  Fixpoint iter_par {S E A} (f : A -> C.t (S * Entropy.t) E unit) (l : list A)
    : C.t (S * Entropy.t) E unit :=
    match l with
    | [] => ret tt
    | x :: l => Concurrency.par_unit (f x) (iter_par f l)
    end.
End List.

Module Event.
  Import Notations.

  Definition t := list.

  Definition loop_seq {S E A} (f : A -> C.t S E unit) : C.t (S * t A) E unit :=
    let! s_events : S * t A := State.read in
    let (s, events) := s_events in
    do! lift_state (List.iter_seq f events) in
    let! s_events : S * t A := State.read in
    let (s, _) := s_events in
    State.write (s, []).

  Definition loop_par {S E A} (f : A -> C.t (S * Entropy.t) E unit)
    : C.t ((S * t A) * Entropy.t) E unit :=
    let! state := State.read in
    match state with
    | ((s, events), bs) =>
      do! map_state
        (fun s => match s with (s1, s2, s3) => (s1, s3, s2) end)
        (fun s => match s with (s1, s2, s3) => (s1, s3, s2) end)
        (lift_state (List.iter_par f events)) in
      let! state := State.read in
      match state with
      | ((s, _), bs) => State.write ((s, []), bs)
      end
    end.

  Module Test.
    Definition log_all (_ : unit) : C.t (Log.t nat * t nat * Entropy.t) Empty_set unit :=
      loop_par (fun n =>
        lift_state (Log.log n)).

    Definition eval (inputs : list nat) (entropy : Entropy.t) : list nat :=
      match snd (eval (log_all tt) ([], inputs, entropy)) with
      | (output, _, _) => output
      end.

    Definition test_1 : eval [] Entropy.left = [] :=
      eq_refl.

    Definition test_2 : eval [1; 2; 3] Entropy.left = [3; 2; 1] :=
      eq_refl.

    Definition test_3 : eval [1; 2; 3] Entropy.right = [1; 2; 3] :=
      eq_refl.
  End Test.
End Event.
