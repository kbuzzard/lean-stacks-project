import algebra.group -- to get letI

class foo (X : Type) :=
(p : Prop)

instance make_foo (X : Type) : foo X := {p := true}

definition foo_and_p (X : Type) (Y : Type) [foo X] [foo Y] : Prop := foo.p X ∧ foo.p Y 

definition bar1 (X : Type) (Y : Type) : foo_and_p X Y := sorry

definition bar2 (X : Type) (Y : Type) :
let HX := make_foo X in
let HY := make_foo Y in
@foo_and_p X Y HX HY := sorry -- typechecks

definition bar3 (X : Type) (Y : Type) [HY : foo Y] :
by letI HX := make_foo X; exact
@foo_and_p X Y _ HY := sorry -- typechecks

definition bar4 (X : Type) (Y : Type) :
by letI HX := make_foo X; exact
by letI HY := make_foo Y; exact
foo_and_p X Y := sorry -- typechecks

definition bar5 (X : Type) :
let Y := ℕ in foo_and_p X Y := sorry
