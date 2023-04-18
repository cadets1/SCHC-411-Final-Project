import Mathlib.Init.Function
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic

namespace final_project

----- Properties of Groups -----

class Group (α : Type) where
  op : α → α → α
  op_assoc : ∀ a b c : α, op a (op b c) = op (op a b) c
  e : α
  e_op : ∀ a : α, op e a = a
  op_e : ∀ a : α, op a e = a
  inv : α → α 
  inv_op : ∀ a : α, op (inv a) a = e
  op_inv : ∀ a : α, op a (inv a) = e

/- Any group is nonempty. -/
theorem nonempty_group (G : Group α) : Nonempty α := by
  apply Nonempty.intro G.e

/- The identity element of a group is unique. -/
theorem unique_identity (G : Group α) (e' : α) : 
    (∀ a : α, G.op e' a = a ∧ G.op a e' = a) → e' = G.e := by
  intro h₁
  have h₂ : G.op G.e e' = e' := by apply G.e_op
  have h₃ : G.op G.e e' = G.e := by exact And.right (h₁ G.e)
  rw [h₂] at h₃
  exact h₃

/- The inverse of any given element of a group is unique. -/
theorem unique_inverse (G : Group α) (a b : α) :
    (G.op a b = G.e ∧ G.op b a = G.e) → b = G.inv a := by
  intro h₁
  have h₂ : G.op (G.inv a) a = G.e := by apply G.inv_op
  have h₃ : G.op a b = G.e := by apply And.left h₁
  have h₄ : G.inv a = G.op (G.inv a) (G.op a b) := by
    rw [h₃]
    apply Eq.symm
    apply G.op_e
  have h₅ : b = G.op (G.op (G.inv a) a) b := by
    rw [h₂]
    apply Eq.symm
    apply G.e_op
  have h₆ : G.op (G.inv a) (G.op a b) = G.op (G.op (G.inv a) a) b := by
    apply G.op_assoc
  rw [←h₄] at h₆
  rw [←h₅] at h₆
  apply Eq.symm
  exact h₆

/- The identity is its own inverse. -/
theorem inverse_identity (G : Group α) : G.inv G.e = G.e := by
  apply Eq.symm
  apply unique_inverse
  apply And.intro
  { exact G.e_op G.e }
  { exact G.e_op G.e }

/- In a group, a*b = a*c → b = c. -/ 
theorem cancellation_property (G : Group α) (a b c : α) : 
    (G.op a b = G.op a c) → b = c := by
  intro h₁
  have h₂ : G.op (G.inv a) (G.op a b) = G.op (G.inv a) (G.op a c) := by
    simp [h₁]
  have h₃ : G.op (G.op (G.inv a) a) b = G.op (G.op (G.inv a) a) c := by
    simp [G.op_assoc] at h₂
    exact h₂
  rw [G.inv_op a] at h₃
  rw [G.e_op b, G.e_op c] at h₃
  exact h₃

/- The power of an element is produced by repeated application of the group operation. -/
def nat_pow (G : Group α) : α → ℕ → α
  | _, 0 => G.e
  | a, n+1 => G.op a (nat_pow G a n)
/- The negative power of an element is defined as a^{-n} = (a^{-1})^n. -/
def neg_pow (G : Group α) : α → ℕ → α :=
  fun a n => nat_pow G (G.inv a) n

/- A group is abelian if its operation is commutative. -/
def abelian {α : Type} (G : Group α) : Prop := 
  ∀ a b : α, G.op a b = G.op b a

/- A group is cyclic if there is a generator g such that 
   every element of the group can be written as a power of g. -/
def cyclic {α : Type} (G : Group α) : Prop :=
  ∃ g : α, ∀ a : α, (∃ n, a = nat_pow G g n) ∨ (∃ m, a = neg_pow G g m)



----- Properties of Group Homomorphisms -----

structure Homomorphism {α β : Type} (G : Group α) (H : Group β) where
  f : α → β
  hom : ∀ x y : α, f (G.op x y) = H.op (f x) (f y)

/- A homomorphism maps the identity to the identity. -/
theorem preserves_identity (h : Homomorphism G H) : h.f G.e = H.e := by
  have h₁ : h.f G.e = h.f (G.op G.e G.e) := by
    simp [G.e_op]
  have h₂ : h.f (G.op G.e G.e) = H.op (h.f G.e) (h.f G.e) := by
    apply h.hom
  have h₃ : h.f G.e = H.op (h.f G.e) (h.f G.e) := by
    apply Eq.trans h₁ h₂
  have h₄ : H.op (h.f G.e) H.e = H.op (h.f G.e) (h.f G.e) := by
    simp [H.op_e]
    exact h₃
  apply Eq.symm
  apply cancellation_property H (h.f G.e) H.e (h.f G.e)
  exact h₄

/- A homomorphism maps inverses to inverses. -/
theorem preserves_inverse (G : Group α) (a : α) (h : Homomorphism G H) : 
    h.f (G.inv a) = H.inv (h.f a) := by
  apply unique_inverse H (h.f a) (h.f (G.inv a))
  apply And.intro
  { have h₁ : H.op (h.f a) (h.f (G.inv a)) = h.f (G.op a (G.inv a)) := by
      apply Eq.symm 
      apply h.hom
    have h₂ : h.f (G.op a (G.inv a)) = H.e := by
      simp [G.op_inv]
      apply preserves_identity h
    apply Eq.trans h₁ h₂ }
  { have h₁ : H.op (h.f (G.inv a)) (h.f a) = h.f (G.op (G.inv a) a) := by
      apply Eq.symm
      apply h.hom
    have h₂ : h.f (G.op (G.inv a) a) = H.e := by
      simp [G.inv_op]
      apply preserves_identity h
    apply Eq.trans h₁ h₂ }

/- A homomorphism φ satisfies φ(a^n) = (φ(a))^n. -/
theorem preserves_nat_power (G : Group α) (a : α) (n : ℕ) (h : Homomorphism G H) : 
    h.f (nat_pow G a n) = nat_pow H (h.f a) n := by
  induction n with
  | zero =>
      simp [nat_pow]
      apply preserves_identity
  | succ n' ih => 
      simp [nat_pow, h.hom]
      rw [ih]

theorem preserves_neg_power (G : Group α) (a : α) (n : ℕ) (h : Homomorphism G H) :
    h.f (neg_pow G a n) = neg_pow H (h.f a) n := by
  simp [neg_pow]
  rw [←preserves_inverse]
  apply preserves_nat_power

/- A homomorphism φ is injective if and only if Ker φ = {e}. -/
theorem injective_kernel (G : Group α) (h : Homomorphism G H) :
    (Function.Injective h.f) ↔ (∀ a : α, h.f a = H.e ↔ a = G.e) := by
  apply Iff.intro
  { intro h₁
    intro a
    have h₂ : h.f G.e = H.e := by apply preserves_identity h
    apply Iff.intro
    { intro h₃
      apply h₁
      rw [←h₂] at h₃
      exact h₃ } 
    { intro h₄
      have h₅ : h.f a = h.f G.e := by simp [h₄]
      apply Eq.trans h₅ h₂ } 
  }
  { intro h₁
    intro a b h₂
    have h₃ : H.op (H.inv (h.f a)) (h.f a) = H.op (H.inv (h.f a)) (h.f b) := by
      simp [h₂]
    have h₄ : H.op (H.inv (h.f a)) (h.f a) = H.e := by
      apply H.inv_op
    have h₅ : H.op (H.inv (h.f a)) (h.f b) = H.e := by
      apply Eq.symm
      rw [←h₄]
      exact h₃
    have h₆ : H.op (h.f (G.inv a)) (h.f b) = H.e := by
      rw [←preserves_inverse G a h] at h₅
      exact h₅ 
    have h₇ : h.f (G.op (G.inv a) b) = H.e := by
      rw [←h.hom] at h₆
      exact h₆
    have h₈ : G.op (G.inv a) b = G.e := by
      simp [h₁] at h₇
      exact h₇
    have h₉ : G.op a (G.op (G.inv a) b) = G.op a G.e := by
      simp [h₈]
    have h' : G.op (G.op a (G.inv a)) b = G.op a G.e := by
      simp [G.op_assoc] at h₉
      exact h₉
    have h'' : b = G.op a G.e := by
      simp [G.op_inv, G.e_op] at h'
      exact h'
    apply Eq.symm
    simp [G.op_e] at h''
    exact h'' }



----- Properties of Isomorphisms -----

structure Isomorphism {α β : Type} (G : Group α) (H : Group β) extends 
    Homomorphism G H where
  inj : Function.Injective f
  sur : Function.Surjective f

/- G is isomorphic to H if there exists some isomorphism from G to H. -/
def Isomorphic (G : Group α) (H : Group β) : Prop :=
  Nonempty (Isomorphism G H)

infixl:60 " ≅ " => Isomorphic

/- 
· Every group is isomorphic to itself.
· The identity function is an isomorphism.
-/ 
theorem isomorphic_refl {α : Type} (G : Group α) : G ≅ G := by
  let f : α → α := fun a => a
  have hom_proof : ∀ x y : α, f (G.op x y) = G.op (f x) (f y) := by
    intro x y
    simp
  have inj_proof : Function.Injective f := by
    intro x y h₁
    simp [h₁]
  have sur_proof : Function.Surjective f := by
    intro y
    apply Exists.intro y
    simp
  apply Nonempty.intro (Isomorphism.mk (Homomorphism.mk f hom_proof) inj_proof sur_proof)
  
/- 
· If G is isomorphic to H, then H is isomorphic to G.
· If φ is an isomorphism from G to H, then the inverse of φ is an isomorphism from H to G.
-/
theorem isomorphic_symm {α β : Type} (G : Group α) (H : Group β) 
    (h : G ≅ H) : H ≅ G := by
  have φ : Isomorphism G H := by apply Classical.choice h
  have h₁ : Function.Bijective φ.f := by
    apply And.intro
    { exact φ.inj }
    { exact φ.sur } 
  have h₂ : ∃ g, Function.LeftInverse g φ.f ∧ Function.RightInverse g φ.f := by
    apply Iff.mp Function.bijective_iff_has_inverse
    exact h₁
  let ⟨g, hg⟩ := Classical.indefiniteDescription 
    (fun x => Function.LeftInverse x φ.f ∧ Function.RightInverse x φ.f) h₂
  have hg_left : Function.LeftInverse g φ.f := by 
    apply And.left hg
  have hg_right : Function.RightInverse g φ.f := by
    apply And.right hg
  have hom_proof : ∀ x y : β, g (H.op x y) = G.op (g x) (g y) := by
    intro c d
    have h₃ : ∃ a : α, φ.f a = c := by apply φ.sur
    have h₄ : ∃ b : α, φ.f b = d := by apply φ.sur
    let ⟨a, ha⟩ := Classical.indefiniteDescription (fun x => φ.f x = c) h₃
    let ⟨b, hb⟩ := Classical.indefiniteDescription (fun x => φ.f x = d) h₄
    have h₅ : φ.f (G.op a b) = H.op c d := by
      simp [φ.hom, ha, hb]
    have h₆ : g (H.op c d) = G.op a b := by
      rw [←h₅]
      apply hg_left
    have h₇ : g c = a := by
      rw [←ha]
      apply hg_left
    have h₈ : g d = b := by
      rw [←hb]
      apply hg_left
    rw [h₆, h₇, h₈]
  have inj_proof : Function.Injective g := by
    apply Function.LeftInverse.injective hg_right
  have sur_proof : Function.Surjective g := by
    apply Function.RightInverse.surjective hg_left
  apply Nonempty.intro (Isomorphism.mk (Homomorphism.mk g hom_proof) inj_proof sur_proof)

/- 
· If G is isomorphic to H and H is isomorphic to K, then G is isomorphic to K.
· If f is an isomorphism from G to H and g is an isomorphism from H to K,
  then g ∘ f is an isomorphism from G to K
-/
theorem isomorphic_trans {α β γ : Type} (G : Group α) (H : Group β) (K : Group γ)
    (h : G ≅ H) (h' : H ≅ K) : G ≅ K := by
  have φ₁ : Isomorphism G H := by apply Classical.choice h
  have φ₂ : Isomorphism H K := by apply Classical.choice h'
  let φ : α → γ := φ₂.f ∘ φ₁.f
  have hom_proof : ∀ x y : α, φ (G.op x y) = K.op (φ x) (φ y) := by
    intro x y
    simp [φ₁.hom, φ₂.hom]
  have inj_proof : Function.Injective φ := by
    apply Function.Injective.comp φ₂.inj φ₁.inj
  have sur_proof : Function.Surjective φ := by
    apply Function.Surjective.comp φ₂.sur φ₁.sur
  apply Nonempty.intro (Isomorphism.mk (Homomorphism.mk φ hom_proof) inj_proof sur_proof)

/- The abelian property of groups is preserved under isomorphism. -/
theorem preserves_abelian {α β : Type} (G : Group α) (H : Group β) (h : G ≅ H) :
    abelian G ↔ abelian H := by
  have φ : Isomorphism G H := by apply Classical.choice h
  apply Iff.intro
  { intro h₁ c d
    have h₂ : ∃ a, φ.f a = c := by apply φ.sur
    have h₃ : ∃ b, φ.f b = d := by apply φ.sur
    let ⟨a, ha⟩ := Classical.indefiniteDescription (fun x => φ.f x = c) h₂
    let ⟨b, hb⟩ := Classical.indefiniteDescription (fun x => φ.f x = d) h₃
    have h₄ : H.op c d = φ.f (G.op a b) := by
      simp [φ.hom, ha, hb]
    have h₅ : H.op d c = φ.f (G.op b a) := by
      simp [φ.hom, ha, hb]
    rw [h₄, h₅, h₁] }
  { intro h₁ a b
    have h₂ : φ.f (G.op a b) = φ.f (G.op b a) := by
      simp [φ.hom]
      apply h₁
    apply φ.inj h₂ }

/- The cyclic property of groups is preserved under isomorphism. -/
theorem preserves_cyclic {α β : Type} (G : Group α) (H : Group β) (h : G ≅ H) :
    cyclic G ↔ cyclic H := by
  have φ : Isomorphism G H := by apply Classical.choice h
  apply Iff.intro
  { intro h₁
    let ⟨g, hg⟩ := Classical.indefiniteDescription 
      (fun x => ∀ a : α, (∃ n, a = nat_pow G x n) ∨ (∃ m, a = neg_pow G x m)) h₁
    apply Exists.intro (φ.f g)
    intro b
    have h₂ : ∃ a, φ.f a = b := by apply φ.sur
    let ⟨a, ha⟩ := Classical.indefiniteDescription (fun x => φ.f x = b) h₂
    cases hg a with
    | inl h₃ =>
        let ⟨n, hn⟩ := Classical.indefiniteDescription (fun x => a = nat_pow G g x) h₃
        apply Or.inl
        apply Exists.intro n
        rw [←preserves_nat_power]
        rw [←hn, ←ha]
    | inr h₄ =>
        let ⟨m, hm⟩ := Classical.indefiniteDescription (fun x => a = neg_pow G g x) h₄
        apply Or.inr
        apply Exists.intro m
        rw [←preserves_neg_power]
        rw [←hm, ←ha] }
  { intro h₁
    let ⟨k, hk⟩ := Classical.indefiniteDescription
      (fun x => ∀ b : β, (∃ n, b = nat_pow H x n) ∨ (∃ m, b = neg_pow H x m)) h₁
    have h₂ : ∃ g, φ.f g = k := by apply φ.sur
    let ⟨g, hg⟩ := Classical.indefiniteDescription (fun x => φ.f x = k) h₂
    apply Exists.intro g
    intro a
    cases hk (φ.f a) with
    | inl h₃ => 
        let ⟨n, hn⟩ := Classical.indefiniteDescription (fun x => φ.f a = nat_pow H k x) h₃
        apply Or.inl
        apply Exists.intro n
        apply φ.inj
        rw [preserves_nat_power]
        rw [hg, hn]
    | inr h₄ =>
        let ⟨m, hm⟩ := Classical.indefiniteDescription (fun x => φ.f a = neg_pow H k x) h₄
        apply Or.inr
        apply Exists.intro m
        apply φ.inj
        rw [preserves_neg_power]
        rw [hg, hm] }