import data.real.basic

namespace challenges

-- basic definitions
def upper_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, s ≤ b }
def lower_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, b ≤ s }
def is_least (S : set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

/-- A set has at most one least upper bound -/
theorem challenge2 (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  cases ha with uba luba, 
  cases hb with ubb lubb, 
  have i := luba b, /- Using the fact that a is least upper bound, we can say that b ≥ a if b is an upper bound (which it is!)-/
  have j := lubb a, /- Same thing tells us that a ≥ b -/
  have k:= i ubb, 
  have l := j uba, 
  linarith, 
end 
theorem challenge2_2 (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  unfold is_lub at ha,
  unfold is_lub at hb,  

  cases ha with ha1 ha2, 
  cases hb with hb1 hb2, 
  apply le_antisymm,  
  {apply ha2, 
  exact hb1,  }, 

  {apply hb2, 
  exact ha1, }
end

end challenges
