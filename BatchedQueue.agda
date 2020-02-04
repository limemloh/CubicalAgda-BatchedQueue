{-# OPTIONS --cubical --safe #-}
module BatchedQueue where

open import Cubical.Foundations.Everything
open import Cubical.Core.Glue
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

private
  variable
    ℓ : Level
    A : Type ℓ

----- List definitions and propositions -----

length : List A → ℕ
length [] = 0
length (x ∷ l) = 1 + length l

-- Snoc defined using ++ from Cubical
infixl 5 _∷ʳ_

_∷ʳ_ : List A → A → List A
xs ∷ʳ x = xs ++ x ∷ []

data SnocView {A : Type ℓ} : List A → Type ℓ where
  nil : SnocView []
  snoc : (x : A) → (xs : List A) → (sx : SnocView xs) → SnocView (xs ∷ʳ x)

snocView : (xs : List A) → SnocView xs
snocView {A = A} xs = helper nil xs
  where
    helper : {l : List A} -> SnocView l -> (r : List A) -> SnocView (l ++ r)
    helper {l} sl [] = subst SnocView (sym (++-unit-r l)) sl
    helper {l} sl (x ∷ r) = let IH = helper (snoc x l sl) r in subst SnocView (++-assoc l (x ∷ []) r) IH

¬snoc≡nil : {x : A} → { xs : List A } → xs ∷ʳ x ≡ [] → ⊥
¬snoc≡nil {xs = []} contra = ¬cons≡nil contra
¬snoc≡nil {xs = x ∷ xs} contra = ¬cons≡nil contra

cons≡rev-snoc : (x : A) → (xs : List A) → x ∷ rev xs ≡ rev (xs ∷ʳ x)
cons≡rev-snoc _ [] = refl
cons≡rev-snoc x (y ∷ ys) = λ i → cons≡rev-snoc x ys i ++ y ∷ []

nil≡nil-isContr : isContr (Path (List A) [] [])
nil≡nil-isContr = refl , ListPath.decodeEncode [] [] -- Thanks to Evan Cavallo for helping us with this one

nil≡nil-isProp : isProp (Path (List A) [] [])
nil≡nil-isProp = hLevelSuc 0 _ nil≡nil-isContr

list≡nil-isProp : {xs : List A} → isProp (xs ≡ [])
list≡nil-isProp {xs = []} = nil≡nil-isProp
list≡nil-isProp {xs = x ∷ xs} = λ p _ → ⊥-elim (¬cons≡nil p)

------ BatchedQueue -------

-- Invariant

Inv : {A : Type ℓ} (f r : List A) → Type ℓ
Inv f r = f ≡ [] → r ≡ []

Inv-isProp : (f r : List A) → isProp (Inv f r)
Inv-isProp f r = λ p q → λ i Hf → list≡nil-isProp (p Hf) (q Hf) i

Inv-f-PathP : ∀ {f f' r : List A} → (p : f ≡ f') →
                (invL : Inv f r) → (invR : Inv f' r) → PathP (λ i → Inv (p i) r) invL invR
Inv-f-PathP {r = r} p invL invR = isProp→PathP (λ i → Inv-isProp (p i) r) invL invR

inv-f-cons : {x : A} → {xs r : List A} → Inv (x ∷ xs) r
inv-f-cons = λ contra → ⊥-elim (¬cons≡nil contra)

inv-f-snoc : {x : A} → {xs r : List A} → Inv (xs ∷ʳ x) r
inv-f-snoc = λ contra → ⊥-elim (¬snoc≡nil contra)

inv-r-nil : {f : List A} → Inv f []
inv-r-nil = λ _ → refl

-- The queue

data BatchedQueue {ℓ} (A : Type ℓ) : Type ℓ where
  queue : (f : List A) → (r : List A) → (inv : Inv f r) → BatchedQueue A
  slide : ∀ s f r invL invR → queue (f ∷ʳ s) r invL ≡ queue f (r ∷ʳ s) invR

example₁ : queue (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) [] inv-f-cons ≡ queue (1 ∷ 2 ∷ []) (4 ∷ 3 ∷ []) inv-f-cons
example₁ = slide 4 (1 ∷ 2 ∷ 3 ∷ []) [] _ inv-f-cons ∙ slide 3 (1 ∷ 2 ∷ []) ([] ∷ʳ 4) _ _

slide-r : ∀ (f r : List A) invL invR → queue f r invL ≡ queue (f ++ rev r) [] invR
slide-r f r invL invR = helper f r invL invR (snocView r)
  where
    helper : ∀ {ℓ} {A : Type ℓ} (f r : List A) invL invR → SnocView r → queue f r invL ≡ queue (f ++ rev r) [] invR
    helper f .[] invL invR nil = λ i → queue (p i) [] (path-inv i)
      where
        p : f ≡ f ++ []
        p = ++-unit-r f ⁻¹
        path-inv : PathP (λ i → Inv (p i) []) invL invR
        path-inv = Inv-f-PathP p invL invR
    helper f .(ys ++ y ∷ []) invL invR (snoc y ys sn) = move-y ∙ IH ∙ q
      where
        move-y : queue f (ys ∷ʳ y) invL ≡ queue (f ∷ʳ y) ys inv-f-snoc
        move-y = (slide y f ys inv-f-snoc invL) ⁻¹
        IH : queue (f ∷ʳ y) ys inv-f-snoc ≡ queue ((f ∷ʳ y) ++ rev ys) [] inv-r-nil
        IH = helper (f ∷ʳ y) ys inv-f-snoc inv-r-nil sn
        p : (f ∷ʳ y) ++ rev ys ≡ f ++ rev (ys ∷ʳ y)
        p = (++-assoc f (y ∷ []) (rev ys)) ∙ (λ i → f ++ (cons≡rev-snoc y ys i))
        path-inv : PathP (λ i → Inv (p i) []) inv-r-nil invR
        path-inv = Inv-f-PathP p inv-r-nil invR
        q : queue ((f ∷ʳ y) ++ rev ys) [] inv-r-nil ≡ queue (f ++ rev (ys ∷ʳ y)) [] invR
        q = λ i → queue (p i) [] (path-inv i)

enqueue : A → BatchedQueue A → BatchedQueue A
enqueue a (queue [] r inv) = queue (a ∷ []) r inv-f-cons
enqueue a (queue (x ∷ xs) r inv) = queue (x ∷ xs) (a ∷ r) inv-f-cons
enqueue a (slide s [] r invL invR i) = proof i
  where
    proof : queue ([] ∷ʳ s) (a ∷ r) inv-f-cons ≡ queue (a ∷ []) (r ∷ʳ s) inv-f-cons
    proof = ⊥-elim (¬snoc≡nil (invR refl))
enqueue a (slide s (x ∷ xs) r invL invR i) = slide s (x ∷ xs) (a ∷ r) inv-f-cons inv-f-cons i

dequeue : BatchedQueue A -> Maybe A × BatchedQueue A
dequeue (queue [] r inv) = (nothing , queue [] r inv)
dequeue (queue (x ∷ []) r inv) = (just x , queue (rev r) [] inv-r-nil)
dequeue (queue (x₁ ∷ x₂ ∷ xs) r inv) = (just x₁ , queue (x₂ ∷ xs) r inv-f-cons)
dequeue (slide s [] r invL invR i) = proof i
  where
    proof : (just s , queue (rev r) [] inv-r-nil) ≡ (nothing , queue [] (r ∷ʳ s) invR)
    proof = ⊥-elim (¬snoc≡nil (invR refl))
dequeue (slide s (x ∷ []) r invL invR i) = (just x , proof i)
  where
    move-r : queue ([] ∷ʳ s) r inv-f-cons ≡ queue (s ∷ rev r) [] inv-f-cons
    move-r = slide-r ([] ∷ʳ s) r inv-f-cons inv-f-cons
    p : s ∷ rev r ≡ rev (r ∷ʳ s)
    p = cons≡rev-snoc s r
    path-inv : PathP (λ j → Inv (p j) []) inv-f-cons inv-r-nil
    path-inv = Inv-f-PathP p inv-f-cons inv-r-nil
    proof : queue ([] ∷ʳ s) r inv-f-cons ≡ queue (rev (r ∷ʳ s)) [] inv-r-nil
    proof = move-r ∙ λ i → queue (p i) [] (path-inv i)
dequeue (slide s (x₁ ∷ x₂ ∷ xs) r invL invR i) = (just x₁ , slide s (x₂ ∷ xs) r inv-f-cons inv-f-cons i)

-- Length/size function
lengthsnoc : (x : A) → (xs : List A) → suc (length xs) ≡ length (xs ∷ʳ x)
lengthsnoc x [] = refl
lengthsnoc x (x₁ ∷ l) i =  1 + lengthsnoc x l i

lengthsnocflip : (x : A) → (l₁ l₂ : List A) → length (l₁ ∷ʳ x) + length l₂ ≡ length l₁ + length (l₂ ∷ʳ x)
lengthsnocflip x [] l i = lengthsnoc x l i
lengthsnocflip x (x₁ ∷ l₁) l₂ i = suc (lengthsnocflip x l₁ l₂ i)

size : BatchedQueue A → ℕ
size (queue [] r inv) = 0
size (queue (x ∷ xs) r inv) =  1 + length xs + length r
size (slide s [] r invL invR i) = proof i
  where proof : (suc (length r)) ≡ 0
        proof = ⊥-elim (¬snoc≡nil (invR refl))
size (slide s (x ∷ xs) r invL invR i) = lengthsnocflip s (x ∷ xs) r i

isEmpty : BatchedQueue A → Bool
isEmpty (queue [] r inv) = true
isEmpty (queue (x ∷ xs) r inv) = false
isEmpty (slide s [] r invL invR i) = proof i
  where proof : false ≡ true
        proof = ⊥-elim (¬snoc≡nil (invR refl))
isEmpty (slide s (x ∷ xs) r invL invR i) = false
