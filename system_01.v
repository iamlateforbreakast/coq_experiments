(* System state structure *)
Record Sw_state : Set := mkSw_state
{
  obt : nat;
}.

Record Hw_state : Set := mkHw_state
{
  eqt_is_on : nat;
}.

Record System : Set := mkSystem
{
  sw : Sw_state;
  hw : Hw_state;
}.

Fixpoint advance_time (d:nat)(s: System) : System :=
match d with
| 0 => s
| S d' => advance_time d' (mkSystem (mkSw_state (s.(sw).(obt) + 1)) s.(hw))
end.

(*mkSystem (mkSw_state (s.(sw).(obt) + 1))*)
(*| S d' => advance_time d' s *)
Definition sw0 : Sw_state := mkSw_state 0.

Definition hw0 : Hw_state := mkHw_state 0.

Definition s0 : System := mkSystem sw0 hw0.

Compute advance_time 10 s0.

(* If we advance the system time 0 time, the system is the same *)
Theorem advance_time_zero : forall s : System, advance_time 0 s = s.
Proof.
 intros s.
 simpl.
 reflexivity.
Qed.

(* If we advance a system time n time, the sw obt is n *)
Theorem advance_time_n : forall (s : System) (n: nat), (advance_time n s) = s.
Proof.
 intros s n.
 induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
