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
  T-if0 : ∀{ T guard then else t } → T ⊢ guard ∷ nat → T ⊢ then ∷ t → T ⊢ else ∷ t → T ⊢ if0 guard then else ∷ t
  T-Par : ∀{ T e1 e2 t1 t2 } → T ⊢ e1 ∷ t1 → T ⊢ e2 ∷ t2 → T ⊢ [ e1 , e2 ] ∷ t1 ⊗ t2

data _×_ (A B : Set ) : Set where
  pair : A → B → A × B

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
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ with eval guard prf v₀ 
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ | zero = eval then prf₁ v₀
eval .(if0 guard then else) (T-if0 {T} {guard} {then} {else} prf prf₁ prf₂) v₀ | suc x = eval else prf₂ v₀
eval .([ e1 , e2 ]) (T-Par {T} {e1} {e2} prf prf₁) v₀ = {!( eval e1 prf v₀ ) × ( eval e2 prf₁ v₀)!}

data Maybe (A : Set ) : Set where
  Nothing : Maybe A
  Just : (a : A) → Maybe A


data WellTyped (T : Tp)(e : Expr) : Set where
  hasType : (S : Tp) → T ⊢ e ∷ S → WellTyped T e
mutual
  infer-type : ∀ T e → Maybe (WellTyped T e)
  infer-type T e = {!!}
  check-type : ∀ T e S → Maybe (T ⊢ e ∷ S)
  check-type T e S = {!!}
