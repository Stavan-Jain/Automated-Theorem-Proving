-- let X, Y, Z be sets.
variables {X Y Z : Type} 

-- a function f : X → Y is *injective* if f(a) = f(b) → a = b for all a,b in X.
def injective (f : X → Y)  : Prop :=
∀ a b : X, f(a) = f(b) → a = b

example : 2 + 2 = 5 := sorry

-- challenge: the composite of two injective functions is injective
theorem challenge1_1
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  rw injective at hf, 
  rw injective at hg, 
  rw injective, 
  intro a, intro b, 
  have i := hf a b, 
  have j := hg (f a) (f b), 
  intro Q, 
  have k := j Q, 
  have r := i k, exact r,  
end

theorem challenge1_2
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  intros a b, 
  intro gf, 
  have i2 := hg (f a) (f b),
  have k := i2 gf,
  have r := hf a b k,
  exact r,    
end

theorem challenge1_3
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  intros a b, 
  intro H, 
  apply hf, 
  apply hg, 
  exact H, 
end