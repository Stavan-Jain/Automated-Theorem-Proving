import data.set.basic

open set

def equivalence_class {X : Type} (R : X → X → Prop) 
(x : X) := {y : X | R x y}

example (X : Type) (R : X → X → Prop) (hR : equivalence R) (x : X) : equivalence_class R x ≠ ∅ :=
begin
  unfold equivalence at hR, 
  unfold equivalence_class , 
  have r:= hR.1, 
  have i := R x , 
  have k := r x, 
  have g:=  nonempty_iff_ne_empty, 
  cases g, 
  apply g_mp, use x, apply k, 
  --apply nonempty.ne_empty, use x, apply k, 
end


