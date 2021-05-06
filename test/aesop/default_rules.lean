import tactic.aesop.default_rules

open tactic.aesop.default_rule (split_hyps)

/-!
# split_hyps

Note: the names of generated hypotheses are more or less arbitrary and should
not be relied upon.
-/

/- We can split product-like types. -/
example {P Q : Prop} {A B : Type}
  (h₁ : P ∧ Q) (h₂ : A × B) (h₃ : pprod A B) : true :=
begin
  split_hyps,
  guard_hyp h₁_1 : P,
  guard_hyp h₁_2 : Q,
  guard_hyp h₂_1 : A,
  guard_hyp h₂_2 : B,
  guard_hyp h₃_1 : A,
  guard_hyp h₃_2 : B,
  trivial
end

/- We can split product-like types under leading Π binders. -/
example {X : Type} {P Q : X → Prop} (h : ∀ x, P x ∧ Q x) : true :=
begin
  split_hyps,
  guard_hyp h_1 : ∀ x, P x,
  guard_hyp h_2 : ∀ x, Q x,
  trivial
end

/- We can split sigma-like types. -/
example {X : Type} {P : X → Prop} {Q : X → Type}
  (h₁ : ∃ x, P x) (h₂ : Σ x, Q x ) (h₃ : psigma Q) (h₄ : subtype P) : true :=
begin
  split_hyps,
  guard_hyp h₁_w : X,
  guard_hyp h₁_h : P h₁_w,
  guard_hyp h₂_fst : X,
  guard_hyp h₂_snd : Q h₂_fst,
  guard_hyp h₃_fst : X,
  guard_hyp h₃_snd : Q h₃_fst,
  guard_hyp h₄_val : X,
  guard_hyp h₄_property : P h₄_val,
  trivial
end

/- Splitting is recursive, so nested products are supported. -/
example {X Y : Type} {Z : Prop} {P Q : X → Y → Prop}
  (h : (∃ x, ∃ y, P x y ∧ Q x y) ∧ Z) : true :=
begin
  split_hyps,
  guard_hyp h_2 : Z,
  guard_hyp h_1_w : X,
  guard_hyp h_1_h_w : Y,
  guard_hyp h_1_h_h_1 : P h_1_w h_1_h_w,
  guard_hyp h_1_h_h_2 : Q h_1_w h_1_h_w,
  trivial
end
