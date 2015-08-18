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

Module Eq.
  Inductive t {S E A} : C.t S E A -> C.t S E A -> Prop :=
  | Value : forall (v : A), t (C.Value v) (C.Value v)
  | Error : forall (e : E), t (C.Error e) (C.Error e)
  | Break : forall xs1 xs2 ss, (forall s, t (xs1 s) (xs2 s)) ->
    t (C.Break xs1 ss) (C.Break xs2 ss).

  Fixpoint reflexivity {S E A} {x : C.t S E A} : t x x.
    destruct x as [v | e | xs ss]; constructor.
    intro s; now apply reflexivity.
  Qed.

  Fixpoint symmetry {S E A} {x1 x2 : C.t S E A} (H : t x1 x2) : t x2 x1.
    destruct H; constructor.
    intro s; now apply symmetry.
  Qed.

  Fixpoint transitivity {S E A} {x1 x2 x3 : C.t S E A}
    (H12 : t x1 x2) (H23 : t x2 x3) : t x1 x3.
    destruct H12; try apply H23.
    inversion H23.
    apply Break.
    intro s; now apply (transitivity _ _ _ _ _ _  (H s)).
  Qed.
End Eq.

Module MonadicLaw.
  Definition neutral_left {S E A B} (x : A) (f : A -> C.t S E B)
    : Eq.t (bind (ret x) f) (f x).
    apply Eq.reflexivity.
  Qed.

  Fixpoint neutral_right {S E A} (x : C.t S E A)
    : Eq.t (bind x ret) x.
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s.
    apply neutral_right.
  Qed.

  Fixpoint associativity {S E A B C}
    (x : C.t S E A) (f : A -> C.t S E B) (g : B -> C.t S E C) {struct x}
    : Eq.t (bind (bind x f) g) (bind x (fun x => bind (f x) g)).
    destruct x as [v | e | xs ss]; simpl; try apply Eq.reflexivity.
    apply Eq.Break; intro s.
    apply associativity.
  Qed.
End MonadicLaw.

(** Raw evaluation. *)
Fixpoint eval {S E A} (x : C.t S E A) (s : S) : (A + E) * S :=
  match C.body x s with
  | Val x => (inl x, s)
  | Err e => (inr e, s)
  | Com (x, s) => eval x s
  end.

(** Augment the state. *)
Fixpoint lift_state {S1 S2 E A} (x : C.t S1 E A) : C.t (S1 * S2) E A :=
  C.New (fun (s : S1 * S2) =>
    let (s1, s2) := s in
    match C.body x s1 with
    | Val x => Val x
    | Err e => Err e
    | Com (x, s1) => Com (lift_state x, (s1, s2))
    end).

(** Apply an isomorphism to the state. *)
Fixpoint map_state {S1 S2 E A} (f : S1 -> S2) (g : S2 -> S1) (x : C.t S1 E A)
  : C.t S2 E A :=
  C.New (fun (s2 : S2) =>
    let s1 := g s2 in
    match C.body x s1 with
    | Val x => Val x
    | Err e => Err e
    | Com (x, s1) => Com (map_state f g x, f s1)
    end).

Module Notations.
  Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End Notations.

Module Option.
  Definition none {A} : C.t unit unit A :=
    C.New (fun _ => Err tt).
End Option.

Module Error.
  Definition raise {E A} (e : E) : C.t unit E A :=
    C.New (fun _ => Err e).
End Error.

Module Log.
  Definition t := list.

  Definition log {A} (x : A) : C.t (t A) Empty_set unit :=
    C.New (fun s => (Val tt, x :: s)).
End Log.

Module State.
  Definition read {S : Type} (_ : unit) : C.t S Empty_set S :=
    C.New (fun s => (Val s, s)).

  Definition write {S : Type} (x : S) : C.t S Empty_set unit :=
    C.New (fun _ => (Val tt, x)).
End State.

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

  (** Executes [x] and [y] concurrently, using a boolean stream as source of entropy. *)
  Fixpoint par {S E A B}
    (x : C.t (S * Entropy.t) E A) (y : C.t (S * Entropy.t) E B) {struct x}
    : C.t (S * Entropy.t) E (A * B) :=
    let fix par_aux y {struct y} : C.t (S * Entropy.t) E (A * B) :=
      C.New (fun (s : S * Entropy.t) =>
        match s with
        | (s, Streams.Cons b bs) =>
          if b then
            let (r, ss) := C.body x (s, bs) in
            (match r with
            | Val x => Com (let! y := y in ret (x, y))
            | Err e => Err e
            | Com x => Com (par x y)
            end, ss)
          else
            let (r, ss) := C.body y (s, bs) in
            (match r with
            | Val y => Com (let! x := x in ret (x, y))
            | Err e => Err e
            | Com y => Com (par_aux y)
            end, ss)
        end) in
    C.New (fun (s : S * Entropy.t) =>
      match s with
      | (s, Streams.Cons b bs) =>
        if b then
          let (r, ss) := C.body x (s, bs) in
          (match r with
          | Val x => Com (let! y := y in ret (x, y))
          | Err e => Err e
          | Com x => Com (par x y)
          end, ss)
        else
          let (r, ss) := C.body y (s, bs) in
          (match r with
          | Val y => Com (let! x := x in ret (x, y))
          | Err e => Err e
          | Com y => Com (par_aux y)
          end, ss)
      end).

  Definition par_unit {S E} (x : C.t (S * Entropy.t) E unit) (y : C.t (S * Entropy.t) E unit)
    : C.t (S * Entropy.t) E unit :=
    let! _ := par x y in
    ret tt.

  (** Make [x] atomic. *)
  Fixpoint atomic {S E A} (x : C.t S E A) : C.t S E A :=
    C.New (fun (s : S) =>
      match C.body x s with
      | (Val _, _) as y | (Err _, _) as y => y
      | (Com x, s) => C.body (atomic x) s
      end).
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
  Definition t := list.

  Definition loop_seq {S E A} (f : A -> C.t S E unit) : C.t (S * t A) E unit :=
    C.New (fun (s : S * t A) =>
      let (s, events) := s in
      (Com (lift_state (List.iter_seq f events)), (s, []))).

  Definition loop_par {S E A} (f : A -> C.t (S * Entropy.t) E unit)
    : C.t (S * t A * Entropy.t) E unit :=
    C.New (fun (s : S * t A * Entropy.t) =>
      match s with
      | (s, events, entropy) =>
        let c := List.iter_par f events in
        let c := lift_state c in
        let c := map_state
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
          c in
        (Com c, (s, [], entropy))
      end).

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
