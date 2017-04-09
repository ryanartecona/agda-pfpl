module SystemT where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; zero; suc; toℕ; raise; #_; inject₁)
open import Data.Vec using (Vec; []; _∷_; lookup; splitAt; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_; _$_)
open import Data.Product

open import Data.Bool using (Bool)
open import Data.Maybe

--------------------------------------------------------------------------------

infixr 30 _⇒_
data TType : Set where
  nat : TType
  _⇒_ : TType → TType → TType

infixl 80 _∙_
data Syntax : Set where
  -- A variable with ℕ as the de Bruijn index
  var : ℕ → Syntax
  -- Natural numbers
  z : Syntax
  s : Syntax → Syntax
  -- Recursion on nats
  rec : Syntax → Syntax → Syntax → Syntax
  -- Lambda abstraction
  lam : TType → Syntax → Syntax
  -- Lambda application
  _∙_ : Syntax → Syntax → Syntax

Ctx : ℕ → Set
Ctx = Vec TType

data Term {n} (Γ : Ctx n) : TType → Set where
  var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ
  z   : Term Γ nat
  s   : Term Γ nat → Term Γ nat
  rec : ∀ {τ} → Term Γ nat → Term Γ τ → Term Γ (nat ⇒ τ ⇒ τ) → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  _∙_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ

Closed : TType → Set
Closed = Term []

test1 : Closed (nat ⇒ nat)
test1 = lam nat
      (rec (var (# 0) refl)
        (z)
        (lam nat
          (lam nat
            (s (s (var (# 1) refl))))))

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase (var v x)     = var (toℕ v)
erase (z)           = z
erase (s t)         = s (erase t)
erase (rec n e₁ e₂) = rec (erase n) (erase e₁) (erase e₂)
erase (lam σ t)     = lam σ (erase t)
erase (l ∙ a)       = erase l ∙ erase a

≡⇒₁ : ∀ {σ σ' τ τ'} → ((σ ⇒ τ) ≡ (σ' ⇒ τ')) → (σ ≡ σ')
≡⇒₁ refl = refl

≡⇒₂ : ∀ {σ σ' τ τ'} → ((σ ⇒ τ) ≡ (σ' ⇒ τ')) → (τ ≡ τ')
≡⇒₂ refl = refl

_≟_ : ∀ (τ : TType) → (σ : TType) → Dec (τ ≡ σ)
nat ≟ nat = yes refl
nat ≟ (x ⇒ y) = no (λ ())
(x ⇒ y) ≟ nat = no (λ ())
(x ⇒ y) ≟ (x' ⇒ y') with x ≟ x' | y ≟ y'
(x ⇒ y) ≟ (x' ⇒ y') | yes refl | yes refl  = yes refl
(x ⇒ y) ≟ (x' ⇒ y') | no x≢x'  | _         = no (λ p → x≢x' (≡⇒₁ p))
(x ⇒ y) ≟ (x' ⇒ y') | _        | (no y≢y') = no (λ p → y≢y' (≡⇒₂ p))

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (toℕ m)
  no  : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : ∀ n m → Fromℕ n m
fromℕ zero b = no b
fromℕ (suc a) zero = yes zero
fromℕ (suc a) (suc b) with fromℕ a b
fromℕ (suc a) (suc .(toℕ m)) | yes m = yes (suc m)
fromℕ (suc a) (suc .(a + m)) | no m = no m

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yes : (τ : TType) (t : Term Γ τ) → Check Γ (erase t)
  no  : {e : Syntax} → Check Γ e

check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t
check {n} Γ (var x) with fromℕ n x
check {n} Γ (var .(toℕ m)) | yes m = yes (lookup m Γ) (var m refl)
check {n} Γ (var .(n + m)) | no m  = no
check {n} Γ (z) = yes nat z
check {n} Γ (s t) with check Γ t
check {n} Γ (s .(erase t)) | yes nat t     = yes nat (s t)
check {n} Γ (s .(erase t)) | yes (_ ⇒ _) t = no
check {n} Γ (s t)          | no            = no
check {n} Γ (rec x e₀ e₁) with check Γ x | check Γ e₀ | check Γ e₁
check {n} Γ (rec .(erase x) .(erase e₀) .(erase e₁)) | yes nat x | yes τ e₀ | yes (nat ⇒ τ' ⇒ τ'') e₁ with τ ≟ τ' | τ ≟ τ''
check {n} Γ (rec .(erase x) .(erase e₀) .(erase e₁)) | yes nat x | yes τ e₀ | yes (nat ⇒ .τ ⇒ .τ) e₁ | yes refl | yes refl = yes τ (rec x e₀ e₁)
check {n} Γ (rec .(erase x) .(erase e₀) .(erase e₁)) | yes nat x | yes τ e₀ | yes (nat ⇒ τ' ⇒ τ'') e₁ | _ | _ = no
check {n} Γ (rec x e₀ e₁) | _ | _ | _ = no
check {n} Γ (lam τ x) with check (τ ∷ Γ) x
check {n} Γ (lam τ .(erase t)) | yes σ t = yes (τ ⇒ σ) (lam τ t)
check {n} Γ (lam τ x) | no = no
check {n} Γ (t ∙ u) with check Γ t | check Γ u
check {n} Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t   | (yes σ' u) with σ ≟ σ'
check {n} Γ (.(erase t) ∙ .(erase u)) | yes (.σ' ⇒ τ) t | (yes σ' u) | (yes refl) = yes τ (t ∙ u)
check {n} Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t   | (yes σ' u) | _          = no
check {n} Γ (t ∙ u)                   | _               | _ = no


⟦_⟧ : TType → Set
⟦ nat ⟧ = ℕ
⟦ x ⇒ y ⟧ = ⟦ x ⟧ → ⟦ y ⟧

-- infixr 5 _∷_
-- data Env : ∀ {n} → Ctx n → Set where
--   [] : Env []
--   _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

-- lookupEnv : ∀ {n} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ lookup m Γ ⟧
-- lookupEnv zero (x ∷ env) = x
-- lookupEnv (suc m) (x ∷ env) = lookupEnv m env

infixr 5 _∷_
data EnvOf : ∀ {n} → (TType → Set) → Ctx n → Set where
  [] : ∀ {f} → EnvOf f []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} {f} → (f τ) → EnvOf f Γ → EnvOf f (τ ∷ Γ)

lookupEnvOf : ∀ {n} {Γ : Ctx n} {f} (m : Fin n) → EnvOf f Γ → f (lookup m Γ)
lookupEnvOf zero (x ∷ env) = x
lookupEnvOf (suc m) (x ∷ env) = lookupEnvOf m env


-- helper for _[_] below
natToT : ∀ {m} {Γ : Ctx m} → ℕ → Term Γ nat
natToT zero = z
natToT (suc n) = s (natToT n)

-- This evaluates a term in a given environment directly,
-- but it (a) doesn't satisfy the termination checker naively,
-- and (b) it eagerly evaluates all rec steps instead of only
-- evaluating necessary steps lazily.
{-# TERMINATING #-}
_[_] : ∀ {m} {Γ : Ctx m} {τ} → EnvOf ⟦_⟧ Γ → Term Γ τ → ⟦ τ ⟧
env [ var v refl ] = lookupEnvOf v env
env [ z ] = 0
env [ s x ] = suc (env [ x ])
env [ rec x e₀ e₁ ] with env [ x ]
env [ rec x e₀ e₁ ] | zero = env [ e₀ ]
env [ rec x e₀ e₁ ] | suc p = (env [ e₁ ]) p (env [ (rec (natToT p) e₀ e₁) ])
env [ lam σ t ] = λ x → (x ∷ env) [ t ]
env [ l ∙ a ] = (env [ l ]) (env [ a ])

-- End of semi-charted territory
--------------------------------------------------------------------------------

data Val {n} (Γ : Ctx n) : TType → Set where
  z : Val Γ nat
  s : Val Γ nat → Val Γ nat
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Val Γ (σ ⇒ τ)

termOf : ∀ {n} {Γ : Ctx n} {τ} → Val Γ τ → Term Γ τ
termOf (z)       = z
termOf (s v)     = s (termOf v)
termOf (lam σ x) = lam σ x

elemToFin
  : ∀ {A : Set} {N} {V : Vec A N} {a : A}
  → (a ∈ V)
  → Fin N
elemToFin _∈_.here = zero
elemToFin (_∈_.there x) = suc (elemToFin x)

finToElem
  : ∀ {A : Set} {n}
  → (i : Fin n)
  → {V : Vec A n}
  → (lookup i V) ∈ V
finToElem () {[]}
finToElem zero {(x ∷ V)} = _∈_.here
finToElem (suc i) {(_ ∷ V)} = _∈_.there (finToElem i)

lookup≡elem
  : ∀ {A : Set} {n} {V : Vec A n} {i} {a : A}
  → a ≡ lookup i V
  → a ∈ V
lookup≡elem {V = V} {i} refl = finToElem i

-- A Ren Γ Γ' is a renaming of indices in Γ to same-type indices in Γ'
Ren
  : ∀ {n m}
  → Ctx n
  → Ctx m
  → Set
Ren {n} {m} Γ Γ' = ∀ {v} → (v ∈ Γ) → (v ∈ Γ')

ren-id
  : ∀ {n} {Γ : Ctx n}
  → Ren Γ Γ
ren-id x = x

ren-lift
  : ∀ {n} {Γ Γ' : Ctx n} {τ}
  → Ren Γ Γ'
  → Ren (τ ∷ Γ) (τ ∷ Γ')
ren-lift ren _∈_.here = _∈_.here
ren-lift ren (_∈_.there x) = _∈_.there (ren x)

∈→F
  : ∀ {n} {A : Set} {V : Vec A n} {v}
  → (e : v ∈ V)
  → v ≡ lookup (elemToFin e) V
∈→F _∈_.here = refl
∈→F (_∈_.there e) = ∈→F e

rename-safety
  : ∀ {n m} {Γ : Ctx n} {Γ' : Ctx m} {τ} {v}
  → (γ : Ren Γ Γ')
  → τ ≡ lookup v Γ
  → τ ≡ lookup (elemToFin (γ (finToElem v))) Γ'
rename-safety {v = v} γ refl with γ (finToElem v)
rename-safety γ refl | _∈_.here = refl
rename-safety γ refl | _∈_.there f = ∈→F f

rename
  : ∀ {n} {Γ Γ' : Ctx n} {τ}
  → Ren Γ Γ'
  → (Term Γ τ → Term Γ' τ)
rename {τ = τ} γ (var v x) = var (elemToFin (γ (finToElem v))) (rename-safety γ x)
rename γ z = z
rename γ (s t) = s (rename γ t)
rename γ (rec t t₁ t₂) = rec (rename γ t) (rename γ t₁) (rename γ t₂)
rename γ (lam σ t) = lam σ (rename (ren-lift γ) t)
rename γ (t ∙ t₁) = rename γ t ∙ rename γ t₁

-- A Subst Γ Γ' is a mapping from variables in Γ to same-typed terms in Γ'
Subst
  : ∀ {n m}
  → Ctx n
  → Ctx m
  → Set
Subst {n} Γ Γ' = ∀ {σ} → (σ ∈ Γ) → Term Γ' σ
-- Subst {n} Γ Γ' = (n' : Fin n) → Term Γ' (lookup n' Γ)

_⇝_ : _
_⇝_ = Subst

subst-id
  : ∀ {n} {Γ : Ctx n}
  → (Γ ⇝ Γ)
subst-id x = var (elemToFin x) (∈→F x)
-- subst-id x = var x refl

subst-lift
  : ∀ {n m} {Γ : Ctx n} {Γ' : Ctx m} {τ}
  → (Γ ⇝ Γ')
  → (Γ ⇝ (τ ∷ Γ'))
subst-lift x y = {!!}
-- subst-lift s₀ zero = var zero refl
-- subst-lift s₀ (suc x) = {!s₀ x!}

remove : ∀ {A : Set} {n} → Fin n → Vec A (suc (n)) → Vec A (n)
remove zero (x ∷ xs) = xs
remove (suc m) (x ∷ xs) = x ∷ remove m xs

-- substₙ : ∀ {n} {Γ : Ctx (suc n)} {σ τ} → Term Γ σ → (m : Fin n) → Term Γ τ → Term (remove m Γ) τ
substₙ
  : ∀ {n} {Γ : Ctx (suc n)} {τ}
  → (m : Fin n)
  → Term Γ (lookup (inject₁ m) Γ)
  → Term Γ τ
  → Term (remove m Γ) τ
substₙ zero x (var zero refl) = {!!}
substₙ (suc m) x (var zero refl) = {!!}
substₙ m x (var (suc v) refl) = {!!}
substₙ m x z = {!!}
substₙ m x (s e) = {!!}
substₙ m x (rec e e₁ e₂) = {!!}
substₙ m x (lam σ e) = {!!}
substₙ m x (e ∙ e₁) = {!!}

insert : ∀ {A : Set} {n} → Fin n → A → Vec A n → Vec A (suc n)
insert zero a xs = a ∷ xs
insert (suc n) a (x ∷ xs) = x ∷ insert n a xs

lower
  : ∀ {n} {Γ : Ctx n} {τ}
  → (m : Fin n)
  → (σ : TType)
  → Term Γ τ
  → Term (insert m σ Γ) τ
lower m σ (var v refl) = {!!}

lower m σ z = z
lower m σ (s t) = s (lower m σ t)
lower m σ (rec t t₁ t₂) = rec (lower m σ t) (lower m σ t₁) (lower m σ t₂)
lower m σ (lam τ t) = lam τ (lower (suc m) σ t)
lower m σ (t ∙ t₁) = lower m σ t ∙ lower m σ t₁

-- subst 0 (z) (lam nat (var 1)) = lam nat (subst 1 (z) (var 1))
-- subst 1 (z) (var 1) = (z)?
-- subst 0 (z) (lam nat (var 0)) = lam nat (subst 1 (z) (var 0))
-- subst 0 (var 0) (lam nat (var 1)) = lam nat (subst 1 (lower 0 nat (var 0)) (var 1))
-- lower 0 nat (var 0) = var 1
-- subst 1 (lower 0 nat (var 0)) (var 1) = subst 1 (var 1) (var 1) = (var 1)

subst
  : ∀ {n} {Γ : Ctx n} {τ}
  → (m : Fin n)
  → Term Γ (lookup m Γ)
  → Term Γ τ
  → Term Γ τ
subst zero x (var zero refl) = x
subst (suc m) x (var zero refl) = {!!}
subst m x (var (suc v) refl) = {!!}
subst m x z = z
subst m x (s e) = s e
subst m x (rec e e₁ e₂) = {!!}
subst m x (lam σ e) = lam σ {!!}
subst m x (e ∙ e₁) = subst m x e ∙ subst m x e₁

-- subst zero (var zero refl) (var zero refl) = var zero refl
-- subst zero (z) (lam nat (var (# 1) refl)) = lam nat (subst (# 1) (z) (var (# 1) refl))

-- [ a / x ] e = subst a x e

data Step {n} {Γ : Ctx n} {τ} (t : Term Γ τ) : Set where
  stepped : Term Γ τ → Step t
  value   : Val Γ τ → Step t

TermEnv : ∀ {n} → (Ctx n) → Set
TermEnv Γ = EnvOf (Term Γ) Γ

-- A small-step dynamics for System T (or attempt thereof...)
step : ∀ {n} {Γ : Ctx n} {τ} → TermEnv Γ → (t : Term Γ τ) → Step t
step env (var v refl) = {!!}
step env z = value z
step env (s t) with step env t
step env (s t) | stepped x = stepped (s x)
step env (s t) | value x = value (s x)
step env (rec x e₁ e₂) with step env x
step env (rec x e₁ e₂) | stepped x₁ = stepped (rec x₁ e₁ e₂)
step env (rec x e₁ e₂) | value z = stepped e₁
step env (rec x e₁ e₂) | value (s x₁) = stepped (e₂ ∙ termOf x₁ ∙ rec (termOf x₁) e₁ e₂)
step env (lam σ t) = {!!}
step env (l ∙ a) with step env l
step env (l ∙ a) | stepped l' = stepped (l' ∙ a)
-- step env (l ∙ a) | value l' = stepped {!!}
step env (l ∙ a) | value l' = stepped {!!}
