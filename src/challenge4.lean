import tactic

open function

theorem challenge4 (X Y Z : Type) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
  unfold surjective, 
  intro h, 
  intro b, -- let b be arbitrary
  have hb := h b, -- this gives us a witness
  cases hb with a gfa, --extracting the witness
  use f a, 
  exact gfa, 
end

theorem challenge4_2 (X Y Z : Type) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
  intro h, 
  intro z, 
  unfold surjective at h, 
  cases h z with a gfa, 
  use f a, 
  assumption, 
end
