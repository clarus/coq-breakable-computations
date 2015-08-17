Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Main.

Import ListNotations.
Import Main.Notations.
Local Open Scope string_scope.

Definition eval_seq (x : C.t (list nat) Empty_set unit) : list nat :=
  snd (eval x []).

Definition eval_par (x : C.t (list nat * Entropy.t) Empty_set unit) (e : Entropy.t) : list nat :=
  fst (snd (eval x ([], e))).

(** Two threads are printing concurrently two lists of numbers. *)
Module PrintList.
  Fixpoint print_before (n : nat) : C.t (Log.t nat) Empty_set unit :=
    match n with
    | O => ret tt
    | S n =>
      let! _ := Log.log n in
      print_before n
    end.

  Definition two_prints_seq (n : nat) : C.t (Log.t nat) Empty_set unit :=
    let! _ := print_before n in
    print_before (2 * n).

  Definition print_before_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
    lift_state (print_before n).

  Definition two_prints_par (n : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
    Concurrency.par_unit (print_before_par n) (print_before_par (2 * n)).

  Definition test_1 : eval_seq (print_before 12) = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.

  Definition test_2 : eval_seq (two_prints_seq 12) = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
    20; 21; 22; 23; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.

  Definition test_3 : eval_par (print_before_par 12) Entropy.half = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.

  Definition test_4 : eval_par (two_prints_par 12) Entropy.left = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
    20; 21; 22; 23; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.

  Definition test_5 : eval_par (two_prints_par 12) Entropy.right = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9;
    10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23] :=
    eq_refl.

  Definition test_6 : eval_par (two_prints_par 12) Entropy.half = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
    20; 21; 22; 23; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.

  Definition test_7 : eval_par (two_prints_par 12) (Entropy.random 0) = [
    0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19;
    20; 21; 22; 23; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11] :=
    eq_refl.
End PrintList.

(** A list of threads are printing a number each. *)
Module ListOfPrints.
  Definition print_seq_seq (n k : nat) : C.t (Log.t nat) Empty_set unit :=
    List.iter_seq (Log.log (A := nat)) (List.seq n k).

  Definition print_seq_par (n k : nat) : C.t (Log.t nat * Entropy.t) Empty_set unit :=
    List.iter_par (fun n => lift_state (Log.log n)) (List.seq n k).

  Definition test_1 : eval_seq (print_seq_seq 10 20) = [
    29; 28; 27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13;
    12; 11; 10] :=
    eq_refl.

  Definition test_2 : eval_par (print_seq_par 10 20) Entropy.left = [
    29; 28; 27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13;
    12; 11; 10] :=
    eq_refl.

  Definition test_3 : eval_par (print_seq_par 10 20) Entropy.right = [
    10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26;
    27; 28; 29] :=
    eq_refl.

  Definition test_4 : eval_par (print_seq_par 10 20) (Entropy.random 12) = [
    24; 28; 29; 22; 27; 25; 26; 21; 20; 23; 16; 19; 17; 18; 15; 14; 13;
    12; 11; 10] :=
    eq_refl.
End ListOfPrints.

(** Simple manager for a list of things to do, with a UI saving data on a server. *)
Module TodoManager.
  (** Event from the UI. *)
  Module UiInput.
    Inductive t : Set :=
    | Add : string -> t
    | Remove : nat -> t.
  End UiInput.

  (** Message to the UI. *)
  Module UiOutput.
    Inductive t :=
    | Make : list string -> t.
  End UiOutput.

  (** Event from the server. *)
  Module ServerInput.
    Inductive t :=
    | Make : list string -> t.
  End ServerInput.

  (** Message to the server. *)
  Module ServerOutput.
    Inductive t :=
    | Make : list string -> t.
  End ServerOutput.

  Module Model.
    (** The model is a list of tasks. *)
    Inductive t :=
    | Make : list string -> t.

    Definition add (task : string) : C.t Model.t Empty_set unit :=
      Concurrency.atomic (
        let! model := State.read tt in
        match model with
        | Model.Make tasks => State.write (Model.Make (task :: tasks))
        end).

    Definition remove (id : nat) : C.t Model.t Empty_set unit :=
      Concurrency.atomic (
        let! model := State.read tt in
        match model with
        | Model.Make tasks => State.write (Model.Make tasks) (* TODO *)
        end).

    Definition get (_ : unit) : C.t Model.t Empty_set Model.t :=
      State.read tt.

    Definition set (model : t) : C.t Model.t Empty_set unit :=
      State.write model.
  End Model.

  (** Send an update to the UI system. *)
  Definition push_ui (_ : unit) : C.t (Model.t * Log.t UiOutput.t) Empty_set unit :=
    let! model := lift_state (Model.get tt) in
    match model with
    | Model.Make tasks =>
      map_state
        (fun ss => match ss with (s1, s2) => (s2, s1) end)
        (fun ss => match ss with (s1, s2) => (s2, s1) end)
        (lift_state (Log.log (UiOutput.Make tasks)))
    end.

  (** Send an update to the server. *)
  Definition push_server (_ : unit) : C.t (Model.t * Log.t ServerOutput.t) Empty_set unit :=
    let! model := lift_state (Model.get tt) in
    match model with
    | Model.Make tasks =>
      map_state
        (fun ss => match ss with (s1, s2) => (s2, s1) end)
        (fun ss => match ss with (s1, s2) => (s2, s1) end)
        (lift_state (Log.log (ServerOutput.Make tasks)))
    end.

  (** Update the UI and the server. *)
  Definition broadcast_model (_ : unit)
    : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
    let c_ui := lift_state (lift_state (push_ui tt)) in
    let c_server := lift_state (map_state
      (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
      (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
      (lift_state (push_server tt))) in
    Concurrency.par_unit c_ui c_server.

  (** Handle an event from the UI. *)
  Definition handle_ui (event : UiInput.t)
    : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
    let lift c :=
      lift_state (lift_state (lift_state c)) in
    match event with
    | UiInput.Add task =>
      let! _ := lift (Model.add task) in
      broadcast_model tt
    | UiInput.Remove id =>
      let! _ := lift (Model.remove id) in
      broadcast_model tt
    end.

  Definition eval_handle_ui (inputs : list UiInput.t) (entropy : Entropy.t)
    : list UiOutput.t * list ServerOutput.t :=
    match snd (eval (Event.loop_par handle_ui) (Model.Make [], [], [], inputs, entropy)) with
    | (_, ui_outputs, server_outputs, _, _) => (ui_outputs, server_outputs)
    end.

  Definition test_ui_1 : eval_handle_ui [] Entropy.left = ([], []) :=
    eq_refl.

  Definition test_ui_2 :
    eval_handle_ui [UiInput.Add "task1"; UiInput.Add "task2"] Entropy.left =
      ([UiOutput.Make ["task2"; "task1"]; UiOutput.Make ["task1"]],
      [ServerOutput.Make ["task2"; "task1"]; ServerOutput.Make ["task1"]]) :=
    eq_refl.

  Definition test_ui_3 :
    eval_handle_ui [UiInput.Add "task1"; UiInput.Add "task2"] Entropy.right =
      ([UiOutput.Make ["task1"; "task2"]; UiOutput.Make ["task2"]],
      [ServerOutput.Make ["task1"; "task2"]; ServerOutput.Make ["task2"]]) :=
    eq_refl.

  (** Handle an event from the server. *)
  Definition handle_server (event : ServerInput.t)
    : C.t (Model.t * Log.t UiOutput.t) Empty_set unit :=
    match event with
    | ServerInput.Make tasks =>
      let! _ := lift_state (Model.set (Model.Make tasks)) in
      push_ui tt
    end.

  Definition eval_handle_server (inputs : list ServerInput.t) (entropy : Entropy.t) : list UiOutput.t :=
    let c := Event.loop_par (fun event => lift_state (handle_server event)) in
    match snd (eval c (Model.Make [], [], inputs, entropy)) with
    | (_, outputs, _, _) => outputs
    end.

  Definition test_server_1 : eval_handle_server [] Entropy.left = [] :=
    eq_refl.

  Definition test_server_2 :
    eval_handle_server [ServerInput.Make ["task1"]; ServerInput.Make ["task2"]] Entropy.left =
      [UiOutput.Make ["task2"]; UiOutput.Make ["task1"]] :=
    eq_refl.

  Definition test_server_3 :
    eval_handle_server [ServerInput.Make ["task1"]; ServerInput.Make ["task2"]] Entropy.right =
      [UiOutput.Make ["task1"]; UiOutput.Make ["task2"]] :=
    eq_refl.

  Definition lifted_handle_server (event : ServerInput.t)
    : C.t (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Entropy.t) Empty_set unit :=
    lift_state (lift_state (handle_server event)).

  Definition State : Type :=
    (Model.t * Log.t UiOutput.t * Log.t ServerOutput.t * Event.t UiInput.t * Event.t ServerInput.t * Entropy.t)%type.

  (** The TODO manager client. *)
  Definition todo (_ : unit) : C.t State Empty_set unit :=
    let c_ui : C.t State Empty_set unit :=
      (* Handle events concurrently. *)
      let c := Event.loop_par handle_ui in
      let c := lift_state c in
      map_state
        (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
        (fun ss => match ss with (s1, s2, s3) => (s1, s3, s2) end)
        c in
    let c_server : C.t State Empty_set unit :=
      (* Handle events concurrently. *)
      let c := Event.loop_par lifted_handle_server in
      let c := lift_state c in
      map_state
        (fun ss => match ss with (s1, s2, s3, s4) => (s1, s4, s2, s3) end)
        (fun ss => match ss with (s1, s2, s3, s4) => (s1, s3, s4, s2) end)
        c in
    Concurrency.par_unit c_ui c_server.

  Definition eval (ui_inputs : list UiInput.t) (server_inputs : list ServerInput.t) (entropy : Entropy.t)
    : list UiOutput.t * list ServerOutput.t :=
    match snd (eval (todo tt) (Model.Make [], [], [], ui_inputs, server_inputs, entropy)) with
    | (_, ui_outputs, server_outputs, _, _, _) => (ui_outputs, server_outputs)
    end.

  Definition test_1 :
    eval [] [] (Entropy.random 12) = ([], []) :=
    eq_refl.

  Definition test_2 :
    eval [UiInput.Add "task1"] [] (Entropy.random 12) =
      ([UiOutput.Make ["task1"]], [ServerOutput.Make ["task1"]]) :=
    eq_refl.

  Definition test_3 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"] [] Entropy.left =
      ([UiOutput.Make ["task2"; "task1"]; UiOutput.Make ["task1"]],
      [ServerOutput.Make ["task2"; "task1"]; ServerOutput.Make ["task1"]]) :=
    eq_refl.

  Definition test_4 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"] [] Entropy.right =
      ([UiOutput.Make ["task1"; "task2"]; UiOutput.Make ["task2"]],
      [ServerOutput.Make ["task1"; "task2"]; ServerOutput.Make ["task2"]]) :=
    eq_refl.

  Definition test_5 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] Entropy.left =
      ([UiOutput.Make ["task3"; "task2"; "task1"];
        UiOutput.Make ["task2"; "task1"]; UiOutput.Make ["task1"]],
      [ServerOutput.Make ["task3"; "task2"; "task1"];
        ServerOutput.Make ["task2"; "task1"]; ServerOutput.Make ["task1"]]) :=
    eq_refl.

  Definition test_6 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] Entropy.right =
      ([UiOutput.Make ["task1"; "task2"; "task3"];
        UiOutput.Make ["task2"; "task3"]; UiOutput.Make ["task3"]],
      [ServerOutput.Make ["task1"; "task2"; "task3"];
        ServerOutput.Make ["task2"; "task3"]; ServerOutput.Make ["task3"]]) :=
    eq_refl.

  Definition test_7 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"; UiInput.Add "task3"] [] (Entropy.random 10) =
      ([UiOutput.Make ["task2"; "task1"; "task3"];
        UiOutput.Make ["task1"; "task3"]; UiOutput.Make ["task3"]],
      [ServerOutput.Make ["task2"; "task1"; "task3"];
        ServerOutput.Make ["task1"; "task3"];
        ServerOutput.Make ["task1"; "task3"]]) :=
    eq_refl.

  Definition test_8 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] Entropy.left =
      ([UiOutput.Make ["task3"]; UiOutput.Make ["task2"; "task1"];
        UiOutput.Make ["task1"]],
      [ServerOutput.Make ["task2"; "task1"]; ServerOutput.Make ["task1"]]) :=
    eq_refl.

  Definition test_9 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] Entropy.right =
      ([UiOutput.Make ["task1"; "task2"; "task3"];
        UiOutput.Make ["task2"; "task3"]; UiOutput.Make ["task3"]],
      [ServerOutput.Make ["task1"; "task2"; "task3"];
        ServerOutput.Make ["task2"; "task3"]]) :=
    eq_refl.

  Definition test_10 :
    eval [UiInput.Add "task1"; UiInput.Add "task2"] [ServerInput.Make ["task3"]] (Entropy.random 10) =
      ([UiOutput.Make ["task1"; "task3"]; UiOutput.Make ["task3"];
        UiOutput.Make ["task2"]],
      [ServerOutput.Make ["task1"; "task3"]; ServerOutput.Make ["task2"]]) :=
    eq_refl.
End TodoManager.
