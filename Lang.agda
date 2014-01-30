module Lang where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
  
{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}


infixr 20 _⇒_
infixl 25 _⊗_

data Tp : Set where
  nat : Tp
  _⇒_ : Tp → Tp → Tp
  _⊗_ : Tp → Tp → Tp

data Expr : Set where
  N : ℕ → Expr
  if0 : Expr → Expr → Expr → Expr
  V : Expr
  lam : Tp → Expr → Expr
  _•_ : Expr → Expr → Expr
  _$_ : Expr → Expr → Expr
  [_,_] : Expr → Expr → Expr
  fst : Expr → Expr
  snd : Expr → Expr

infix 10 _⊢_∷_

data _⊢_∷_ : Tp → Expr → Tp → Set where
  T-Nat : ∀{ T n } → T ⊢ N n ∷ nat
  T-Var : ∀{ T } → T ⊢ V ∷ T
  T-fst : ∀{ T e t1 t2 } → T ⊢ e ∷ (t1 ⊗ t2) → T ⊢ fst e ∷ t1
  T-snd : ∀{ T e t1 t2 } → T ⊢ e ∷ (t1 ⊗ t2) → T ⊢ snd e ∷ t2
  T-lam : ∀{ T t e1 t1 } → t ⊢ e1 ∷ t1 → T ⊢ lam t e1 ∷ t ⇒ t1
  T-tim : ∀{ T f g a b c } → T ⊢ f ∷ b ⇒ c → T ⊢ g ∷ a ⇒ b → T ⊢ f • g ∷ a ⇒ c
  T-apl : ∀{ T f a ta tb} → T ⊢ f ∷ ta ⇒ tb → T ⊢ a ∷ ta → T ⊢ f $ a ∷ tb 
  T-if0 : ∀{ T guard then else t } → T ⊢ guard ∷ nat → T ⊢ then ∷ t → T ⊢ else ∷ t → T ⊢ if0 guard then else ∷ t
  T-Par : ∀{ T e1 e2 t1 t2 } → T ⊢ e1 ∷ t1 → T ⊢ e2 ∷ t2 → T ⊢ [ e1 , e2 ] ∷ t1 ⊗ t2

data _×_ (A B : Set ) : Set where
  pair : A → B → A × B
  
_⊖_ : {A B : Set} → A → B → A × B
x ⊖ y = pair x y

⟦_⟧ : Tp → Set
⟦ nat ⟧ = ℕ
⟦ x ⇒ x₁ ⟧ = ⟦ x ⟧ → ⟦ x₁ ⟧
⟦ x ⊗ x₁ ⟧ =  ⟦ x ⟧ × ⟦ x₁ ⟧

eval : { T S : Tp } → (e : Expr) → T ⊢ e ∷ S → ⟦ T ⟧ → ⟦ S ⟧
eval .(N n) (T-Nat {T} {n}) v₀ = n
eval .V T-Var v₀ = v₀
eval .(fst e) (T-fst {T} {e} prf) v₀ with eval e prf v₀ 
eval .(fst e) (T-fst {T} {e} prf) v₀ | pair x x₁ = x
eval .(snd e) (T-snd {T} {e} prf) v₀ with eval e prf v₀
eval .(snd e) (T-snd {T} {e} prf) v₀ | pair x x₁ = x₁
eval .(lam t e1) (T-lam {T} {t} {e1} prf) v₀ = λ x → eval e1 prf x
eval .(f • g) (T-tim {T} {f} {g} prf prf₁) v₀ = λ a → eval f prf v₀ (eval g prf₁ v₀ a) 
eval .(f $ a) (T-apl {T} {f} {a} prf prf₁) v₀ = (eval f prf v₀) (eval a prf₁ v₀)
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ with eval guard prf v₀ 
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ | zero = eval then prf₁ v₀
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ | suc x = eval else prf₂ v₀
eval .([ e1 , e2 ]) (T-Par {T} {e1} {e2} prf prf₁) v₀ =  eval e1 prf v₀  ⊖  eval e2 prf₁ v₀

data Maybe (A : Set ) : Set where
  Nothing : Maybe A
  Just : (a : A) → Maybe A

_&&_ : {A B : Set} → Maybe A → Maybe B → Maybe (A × B)
infixl 15 _&&_
Nothing && y = Nothing
Just a && Nothing = Nothing
Just a && Just a₁ = Just (a ⊖ a₁)
 
data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

_≟_ : (a b : Tp) → Maybe (a ≡ b) 
infix 20 _≟_
nat ≟ nat = Just refl
nat ≟ (y ⇒ y₁) = Nothing
nat ≟ y ⊗ y₁ = Nothing
(x ⇒ x₁) ≟ nat = Nothing
(x ⇒ x₁) ≟ (y ⇒ y₁) with x ≟ y && x₁ ≟ y₁ 
(x ⇒ x₁) ≟ (y ⇒ y₁) | Nothing = Nothing
(.y ⇒ .y₁) ≟ (y ⇒ y₁) | Just (pair refl refl) = Just refl
(x ⇒ x₁) ≟ y ⊗ y₁ = Nothing
x ⊗ x₁ ≟ nat = Nothing
x ⊗ x₁ ≟ (y ⇒ y₁) = Nothing
x ⊗ x₁ ≟ y ⊗ y₁ with x ≟ y && x₁ ≟ y₁
x ⊗ x₁ ≟ y ⊗ y₁ | Nothing = Nothing
.y ⊗ .y₁ ≟ y ⊗ y₁ | Just (pair refl refl) = Just refl

data WellTyped (T : Tp)(e : Expr) : Set where
  hasType : (S : Tp) → T ⊢ e ∷ S → WellTyped T e
mutual
  infer-type : ∀ T e → Maybe (WellTyped T e)
  infer-type T (N x) = Just (hasType nat (T-Nat {T} {x}))
  infer-type T (if0 e e₁ e₂) with check-type T e nat && infer-type T e₁
  infer-type T (if0 e e₁ e₂) | Nothing = Nothing
  infer-type T (if0 e e₁ e₂) | Just (pair x (hasType S x₁)) with check-type T e₂ S
  infer-type T (if0 e e₁ e₂) | Just (pair x (hasType S x₁)) | Nothing = Nothing
  infer-type T (if0 e e₁ e₂) | Just (pair x (hasType S x₁)) | Just a = Just (hasType S (T-if0 x x₁ a))
  infer-type T V = Just (hasType T T-Var) 
  infer-type T (lam x e) with infer-type x e 
  infer-type T (lam x e) | Nothing = Nothing
  infer-type T (lam x₁ e) | Just (hasType S x) = Just (hasType (x₁ ⇒ S) (T-lam x))
  infer-type T (e • e₁) with infer-type T e 
  infer-type T (e • e₁) | Nothing = Nothing
  infer-type T (e • e₁) | Just (hasType nat x) = Nothing
  infer-type T (e • e₁) | Just (hasType (S ⊗ S₁) x) = Nothing
  infer-type T (e • e₁) | Just (hasType (S ⇒ S₁) x) with infer-type T e₁ 
  infer-type T (e • e₁) | Just (hasType (S ⇒ S₁) x) | Nothing = Nothing
  infer-type T (e • e₁) | Just (hasType (S₁ ⇒ S₂) x₁) | Just (hasType nat x) = Nothing
  infer-type T (e • e₁) | Just (hasType (S₂ ⇒ S₃) x₁) | Just (hasType (S ⊗ S₁) x) = Nothing
  infer-type T (e • e₁) | Just (hasType (S₂ ⇒ S₃) x₁) | Just (hasType (S ⇒ S₁) x) with S₁ ≟ S₂ 
  infer-type T (e • e₁) | Just (hasType (S₂ ⇒ S₃) x₁) | Just (hasType (S ⇒ S₁) x) | Nothing = Nothing
  infer-type T (e • e₁) | Just (hasType (S₂ ⇒ S₃) x₁) | Just (hasType (S ⇒ .S₂) x) | Just refl = Just (hasType (S ⇒ S₃) (T-tim x₁ x))
  infer-type T (f $ a) with infer-type T f
  infer-type T (f $ a) | Nothing = Nothing
  infer-type T (f $ a₁) | Just (hasType nat x) = Nothing
  infer-type T (f $ a₁) | Just (hasType (S ⊗ S₁) x) = Nothing
  infer-type T (f $ a₁) | Just (hasType (S ⇒ S₁) x) with check-type T a₁ S
  infer-type T (f $ a₁) | Just (hasType (S ⇒ S₁) x) | Nothing = Nothing
  infer-type T (f $ a₁) | Just (hasType (S ⇒ S₁) x) | Just a = Just (hasType S₁ (T-apl x a))
  infer-type T [ e , e₁ ] with infer-type T e && infer-type T e₁ 
  infer-type T [ e , e₁ ] | Nothing = Nothing
  infer-type T [ e , e₁ ] | Just (pair (hasType S x) (hasType S₁ x₁)) = Just (hasType (S ⊗ S₁) (T-Par x x₁))
  infer-type T (fst e) with infer-type T e
  infer-type T (fst e) | Nothing = Nothing
  infer-type T (fst e) | Just (hasType nat x) = Nothing
  infer-type T (fst e) | Just (hasType (S ⇒ S₁) x) = Nothing
  infer-type T (fst e) | Just (hasType (S ⊗ S₁) x) = Just (hasType S (T-fst x))
  infer-type T (snd e) with infer-type T e
  infer-type T (snd e) | Nothing = Nothing
  infer-type T (snd e) | Just (hasType nat x) = Nothing
  infer-type T (snd e) | Just (hasType (S ⇒ S₁) x) = Nothing
  infer-type T (snd e) | Just (hasType (S ⊗ S₁) x) = Just (hasType S₁ (T-snd x))

  check-type : ∀ T e S → Maybe (T ⊢ e ∷ S)
  check-type T e S with infer-type T e
  check-type T e S | Nothing = Nothing
  check-type T e S₁ | Just (hasType S x) with S₁ ≟ S
  check-type T e S₁ | Just (hasType S x) | Nothing = Nothing
  check-type T e .S | Just (hasType S x) | Just refl = Just x

interp : (e : Expr) → Maybe ℕ
interp e with infer-type nat e
interp e | Nothing = Nothing
interp e | Just (hasType nat x) = Just ( eval e x 0 )
interp e | Just (hasType (S ⇒ S₁) x) = Nothing
interp e | Just (hasType (S ⊗ S₁) x) = Nothing
