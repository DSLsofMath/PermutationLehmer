\begin{code}
module Permutation where
open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Function using (id; _∘_; _⇔_; mk⇔)
open import Function.Bundles using (Equivalence)
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Fin using (Fin; zero; suc; inject₁)
open import Data.Fin.Properties using () renaming (suc-injective to suc-inj)
open import Data.Vec using (Vec; []; _∷_; tabulate; lookup)
open import Data.Vec.Properties using (lookup∘tabulate; tabulate∘lookup; tabulate-cong)
    renaming
    (∷-injectiveˡ to ∷-inj-head ;
     ∷-injectiveʳ to ∷-inj-tail)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; cong ; cong₂ ; _≢_ ; sym; inspect; [_])
open Relation.Binary.PropositionalEquality.≡-Reasoning

--------------------------------------------------------------------------------
                       --- Prelude and utils ---
--------------------------------------------------------------------------------

variable
  n : ℕ
  A : Set

use-as-definition : {A : Set} {x : A} → x ≡ x
use-as-definition = refl

infix 6 _≐_
_≐_ : {A B : Set} → (A → B) → (A → B) → Set
_≐_ {A} f g = ∀ (x : A) → f x ≡ g x

\end{code}

<<permutationF>>
\begin{code}
PermutationF : ℕ → Set
PermutationF n = Fin n → Fin n
\end{code}

\begin{code}
module PermutationFexample where
\end{code}

<<permutationF-example-swap>>
\begin{code}
  swap2 : Fin 2 -> Fin 2
  swap2 zero        = suc zero
  swap2 (suc zero)  = zero
\end{code}

<<permutationF-nonexample-const>>
\begin{code}
  const : Fin 2 -> Fin 2
  const _           = zero
\end{code}

The function |swap i| transposes the two adjacent positions |i|, |i+1| in
|Fin (suc n)|, leaving everything else fixed. Compositions of swaps is
enough to express all permutations.
<<swap>>
\begin{code}
  swap : Fin n → Fin (suc n) → Fin (suc n)
  swap zero     zero           = suc zero
  swap zero     (suc zero)     = zero
  swap zero     (suc (suc k))  = suc (suc k)
  swap (suc i)  zero           = zero
  swap (suc i)  (suc j)        = suc (swap i j)
\end{code}



<<PermutationVec>>
\begin{code}
PermutationV : ℕ → Set
PermutationV n = Vec (Fin n) n
\end{code}

\begin{code}
module PermutationVexample where
\end{code}

<<permutationV-example-const>>
\begin{code}
  const : Vec (Fin 2) 2
  const = zero ∷ zero ∷ []
\end{code}

--------------------------------------------------------------------------------
        --- Permutations, identity, composition and inverses ---
--------------------------------------------------------------------------------
\begin{code}
module Permutations where
\end{code}

<<permutation>>
\begin{code}
  data Permutation : ℕ → Set where
    nil   : Permutation zero
    _:-_  : Fin (suc n) → Permutation n → Permutation (suc n)
\end{code}

\begin{code}
  infixr 6 _:-_
\end{code}

The function |skip| is the same as |Data.Fin.punchIn| but we like the name skip better.

<<skip>>
\begin{code}
  skip : Fin (suc n) → Fin n →  Fin (suc n)
  skip zero      i       = suc i
  skip (suc j)  zero     = zero
  skip (suc j)  (suc i)  = suc (skip j i)
\end{code}

The function |pinch| is also available as |Data.Fin.pinch|.

<<pinch>>
\begin{code}
  pinch : Fin n → Fin (suc n) → Fin n
  pinch {suc n}  _        zero     = zero
  pinch {suc n}  zero     (suc j)  = j
  pinch {suc n}  (suc i)  (suc j)  = suc (pinch i j)
\end{code}

Pinch needs the extra pattern match on the argument n... Otherwise:

    pinch : Fin n → Fin (suc n) → Fin n
    pinch _        zero     = zero  -- For this case to work n must not be zero
    pinch zero     (suc j)  = j
    pinch (suc i)  (suc j)  = suc (pinch i j)

<<semantics>>
\begin{code}
  ⟦_⟧ : Permutation n → (Fin n → Fin n)
  ⟦ p :- ps ⟧  zero     = p
  ⟦ p :- ps ⟧  (suc i)  = skip p (⟦ ps ⟧ i)
\end{code}

<<permutation-id>>
\begin{code}
  idₚ : {n : ℕ} → Permutation n
  idₚ {zero}   = nil
  idₚ {suc n}  = zero :- idₚ
\end{code}

<<permutation-example>>
\begin{code}
  zeros : (n : ℕ) → Permutation n
  zeros zero     = nil
  zeros (suc n)  = zero :- zeros n
\end{code}

<<id-is-id>>
\begin{code}
  idₚ-is-id : forall {n} → ⟦ idₚ {n} ⟧ ≐ id
  idₚ-is-id zero    = refl
  idₚ-is-id (suc i) = cong suc (idₚ-is-id i)
\end{code}

<<remove>>
\begin{code}
  remove : Fin (suc n) → Permutation (suc n) → Permutation n
  remove              zero     (p :- ps)  = ps
  remove {n = suc _}  (suc i)  (p :- ps)  = pinch (⟦ ps ⟧ i) p :- remove i ps
\end{code}

<<compose>>
\begin{code}
  _⊙_ : Permutation n → Permutation n → Permutation n
  nil  ⊙  nil        =  nil
  ps   ⊙  (q :- qs)  = (⟦ ps ⟧ q) :- (remove q ps ⊙ qs)
\end{code}

<<injectivity-lemmas>>
\begin{code}
  skip-skips : (i : Fin n) (j : Fin (suc n)) → skip j i ≢ j
  skip-skips i zero ()
  skip-skips zero (suc j) ()
  skip-skips (suc i) (suc j) = skip-skips i j ∘ suc-inj

  skip-inj : (i : Fin (suc n)) {j j' : Fin n} → skip i j ≡ skip i j' → j ≡ j'
  skip-inj zero                      = suc-inj
  skip-inj (suc i) {zero}  {zero}    = λ {refl → refl}
  skip-inj (suc i) {suc j} {suc j'}  = cong suc ∘ skip-inj i ∘ suc-inj

  skip-inj-eq : {i i' : Fin (suc n)} {j j' : Fin n} → i ≡ i' → skip i j ≡ skip i' j' → j ≡ j'
  skip-inj-eq {i = i} refl = skip-inj i

  apply-inj : (ps : Permutation n) (i j : Fin n) → ⟦ ps ⟧ i ≡ ⟦ ps ⟧ j → i ≡ j
  apply-inj (p :- ps) zero     zero     eq = refl
  apply-inj (p :- ps) zero     (suc j)  eq = ⊥-elim (skip-skips _ _ (sym eq))
  apply-inj (p :- ps) (suc i)  zero     eq = ⊥-elim (skip-skips _ _ eq)
  apply-inj (p :- ps) (suc i)  (suc j)  eq = cong suc (apply-inj ps i j (skip-inj p eq))
\end{code}

<<semantics-injective>>
\begin{code}
  ⟦inj⟧ : ∀ {ps qs : Permutation n} → ⟦ ps ⟧ ≐ ⟦ qs ⟧ → ps ≡ qs
\end{code}

\begin{code}
  ⟦inj⟧ {zero}   {nil}      {nil}      _      = refl
  ⟦inj⟧ {suc n}  {p :- ps}  {q :- qs}   ext-eq =
    let p≡q   = ext-eq zero in
    let ps≐qs = skip-inj-eq p≡q ∘ ext-eq ∘ suc in
    cong₂ _:-_ p≡q (⟦inj⟧ ps≐qs)
\end{code}

These lemmas are used to prove skip-apply
<<properties>>
\begin{code}
  skip-pinch : (i : Fin (suc n)) (j : Fin n) →  i ≡ skip (skip i j) (pinch j i)
  skip-pinch {n = suc n} zero     j         = refl
  skip-pinch {n = suc n} (suc i)  zero      = refl
  skip-pinch {n = suc n} (suc i)  (suc j)   = cong suc (skip-pinch i j)

  skip-assoc : (i : Fin n) (j : Fin (suc n)) (k : Fin (suc (suc n))) →
    skip k (skip j i) ≡ skip (skip k j) (skip (pinch j k) i)
  skip-assoc i        j        zero     = refl
  skip-assoc i        zero     (suc k)  = refl
  skip-assoc zero     (suc j)  (suc k)  = refl
  skip-assoc (suc i)  (suc j)  (suc k)  = cong suc (skip-assoc i j k)
\end{code}

Key lemma used in the correctness of composition
<<skip-apply>>
\begin{code}
  skip-apply : (qs : Permutation (suc n)) (j : Fin (suc n)) →
    ⟦ qs ⟧ ∘ skip j ≐ skip (⟦ qs ⟧ j) ∘ ⟦ remove j qs ⟧
\end{code}

\begin{code}
  skip-apply (q :- qs) zero     i        = refl
  skip-apply (q :- qs) (suc j)  zero     = skip-pinch q (⟦ qs ⟧ j)
  skip-apply (q :- qs) (suc j)  (suc i)  =
      ⟦ q :- qs ⟧ (skip (suc j) (suc i))
    ≡⟨ refl ⟩
      ⟦ q :- qs ⟧ (suc (skip j i))
    ≡⟨ refl ⟩
      skip q (⟦ qs ⟧ (skip j i))
    ≡⟨ cong (skip q) (skip-apply qs j i) ⟩
      skip q (skip (⟦ qs ⟧ (j)) (⟦ remove j qs ⟧ i))
    ≡⟨ skip-assoc (⟦ remove j qs ⟧ i) (⟦ qs ⟧ j) q  ⟩
      skip (skip q (⟦ qs ⟧ j)) (skip (pinch (⟦ qs ⟧ j) q) (⟦ remove j qs ⟧ i))
    ≡⟨ refl ⟩
      skip (⟦ q :- qs ⟧ (suc j)) (⟦ remove (suc j) (q :- qs) ⟧ (suc i))
    ∎
\end{code}

<<unused-properties>> but some are still interesting...
\begin{code}
  pinch-inverts : (i : Fin n) (j : Fin (suc n)) → i ≡ pinch i (skip j i)
  pinch-inverts zero zero = refl
  pinch-inverts zero (suc j) = refl
  pinch-inverts (suc i) zero = cong suc (pinch-inverts i zero)
  pinch-inverts (suc i) (suc j) = cong suc (pinch-inverts i j)
\end{code}

<<pinch-skip-prop>>
\begin{code}
  pinch-skip : (i : Fin n) → pinch i ∘ skip (suc i) ≐ id
\end{code}

<<pinch-skip-proof>>
\begin{code}
  pinch-skip zero zero = refl
  pinch-skip zero (suc j) = refl
  pinch-skip (suc i) zero = refl
  pinch-skip (suc i) (suc j) = cong suc (pinch-skip i j)

  pinch-skip-inj : (i : Fin n) → pinch i ∘ skip (inject₁ i) ≐ id
  pinch-skip-inj zero zero = refl
  pinch-skip-inj zero (suc j) = refl
  pinch-skip-inj (suc i) zero = refl
  pinch-skip-inj (suc i) (suc j) = cong suc (pinch-skip-inj i j)

  pinch-skip0 : {n : ℕ} → pinch (zero {n}) ∘ skip zero ≐ id
  pinch-skip0 j = refl
\end{code}

<<compose-correct>>
\begin{code}
  compose-correct : (ps qs : Permutation n) → ⟦ ps ⟧ ∘ ⟦ qs ⟧ ≐ ⟦ ps ⊙ qs ⟧
\end{code}

<<compose-calculation>>
\begin{code}
  compose-correct {n = suc _} ps@(_ :- _) (q :- qs) zero =
      ⟦ ps ⟧ (⟦ q :- qs ⟧ zero)
    ≡⟨ refl ⟩
      ⟦ ps ⟧ q
    ≡⟨ refl ⟩
      ⟦ ⟦ ps ⟧ q :- (remove q ps) ⊙ qs  ⟧ zero
    ≡⟨ refl  ⟩
      ⟦ ps ⟧ q
    ≡⟨ use-as-definition ⟩
      ⟦ ps ⊙ (q :- qs) ⟧ zero
    ∎

  compose-correct qs@(_ :- _) (p :- ps) (suc i) =
      ⟦ qs ⟧ (⟦ p :- ps ⟧ (suc i))
    ≡⟨ refl ⟩
      ⟦ qs ⟧ (skip p (⟦ ps ⟧ i))
    ≡⟨ skip-apply qs p (⟦ ps ⟧ i) ⟩
      skip (⟦ qs ⟧ p) (⟦ remove p qs ⟧ (⟦ ps ⟧ i))
    ≡⟨ cong (skip _) (compose-correct (remove p qs) ps i) ⟩
      skip (⟦ qs ⟧ p) (⟦ (remove p qs) ⊙ ps ⟧ i)
    ≡⟨ use-as-definition ⟩
      ⟦ qs ⊙ (p :- ps) ⟧ (suc i)
    ∎
\end{code}

<<compose-ids>>
\begin{code}
  compose-id₁    : (ps : Permutation n) → idₚ  ⊙ ps  ≡ ps
  compose-id₂    : (ps : Permutation n) → ps   ⊙ idₚ  ≡ ps
  compose-assoc  : (ps qs rs : Permutation n) → (ps ⊙ qs) ⊙ rs ≡ ps ⊙ (qs ⊙ rs)
\end{code}

\begin{code}
  compose-id₁ ps = ⟦inj⟧ (λ i →
      ⟦ idₚ ⊙ ps ⟧ i
    ≡⟨ sym (compose-correct idₚ ps i) ⟩
      ⟦ idₚ ⟧ (⟦ ps ⟧ i)
    ≡⟨ idₚ-is-id (⟦ ps ⟧ i) ⟩
      id (⟦ ps ⟧ i)
    ≡⟨ refl ⟩
      ⟦ ps ⟧ i
    ∎)


  compose-id₂ ps = ⟦inj⟧ (λ i →
      ⟦ ps ⊙ idₚ ⟧ i
    ≡⟨ sym (compose-correct ps idₚ i) ⟩
      ⟦ ps ⟧ (⟦ idₚ ⟧ i)
    ≡⟨ cong ⟦ ps ⟧ (idₚ-is-id i) ⟩
      ⟦ ps ⟧ (id i)
    ≡⟨ refl ⟩
      ⟦ ps ⟧ i
    ∎)
\end{code}

<<compose-assoc>>
\begin{code}
  compose-assoc ps qs rs = ⟦inj⟧ λ i →
      ⟦ (ps ⊙ qs) ⊙ rs ⟧ i
    ≡⟨ sym (compose-correct (ps ⊙ qs) rs i) ⟩
      ⟦ ps ⊙ qs ⟧ (⟦ rs ⟧ i)
    ≡⟨ sym (compose-correct ps qs (⟦ rs ⟧ i)) ⟩
      ⟦ ps ⟧ (⟦ qs ⟧ (⟦ rs ⟧ i))
    ≡⟨ cong ⟦ ps ⟧ (compose-correct qs rs i) ⟩
      ⟦ ps ⟧ (⟦ qs ⊙ rs ⟧ i)
    ≡⟨ compose-correct ps (qs ⊙ rs) i ⟩
      ⟦ ps ⊙ (qs ⊙ rs) ⟧ i
    ∎
\end{code}


<<unzero>>
\begin{code}
  unzero : Permutation (suc n) → Fin (suc n)
  unzero          (zero   :- ps)  = zero
  unzero {suc n}  (suc x  :- ps)  = suc (unzero ps)
\end{code}

\begin{code}
  unzero-zero : {n : ℕ} → (ps : Permutation n) → unzero (zero :- ps) ≡ zero
  unzero-zero {zero} nil  = refl
  unzero-zero {suc n} ps = refl

  unzero-suc : {n : ℕ}
    (p : Fin (suc n))
    (ps : Permutation (suc n)) → unzero (suc p :- ps) ≡ suc (unzero ps)
  unzero-suc {n} p ps = refl

  unzero-correct : (ps : Permutation (suc n)) →
    ⟦ ps ⟧ (unzero ps) ≡ zero
  unzero-correct (zero :- ps) = refl
  unzero-correct {suc n} (suc p :- ps) =
    skip (suc p) (⟦ ps ⟧ (unzero ps))
      ≡⟨ cong (skip (suc p)) (unzero-correct ps) ⟩
    skip (suc p) zero
      ≡⟨ refl ⟩
    zero ∎
\end{code}

<<inverse>>
\begin{code}
  inverse : Permutation n → Permutation n
  inverse {zero}   nil  =  nil
  inverse {suc n}  ps   =  let p = unzero ps in p :- inverse (remove p ps)
\end{code}

\begin{code}
  inverse-nil : inverse nil ≡ nil
  inverse-nil = refl

  inverse-∷ : (ps : Permutation (suc n)) →
    inverse ps ≡ unzero ps :- inverse (remove (unzero ps) ps)
  inverse-∷ ps = refl
\end{code}

<<inverse-properties>>
\begin{code}
  inverse-id     : inverse idₚ ≡ idₚ {n}
  inverse-prop₁  : (ps : Permutation n) → ps ⊙ (inverse ps) ≡ idₚ
  inverse-prop₂  : (ps : Permutation n) → (inverse ps) ⊙ ps ≡ idₚ
\end{code}

\begin{code}
  inverse-id {zero} = inverse-nil
  inverse-id {suc n} = cong₂ _:-_ refl inverse-id

  inverse-prop₁ {n} nil = refl
  inverse-prop₁ {suc n} (p :- ps) =
    let p₀ = unzero (p :- ps) in
    let ih = inverse-prop₁ (remove p₀ (p :- ps)) in
    ⟦ p :- ps ⟧ p₀ :- (remove p₀ (p :- ps) ⊙ inverse (remove p₀ (p :- ps)))
      ≡⟨ cong₂ _:-_ (unzero-correct (p :- ps)) ih ⟩
    zero :- idₚ ∎

  skip-suc-zero : (i : Fin (suc n)) (j : Fin (suc n)) → j ≡ zero → skip (suc i) j ≡ zero
  skip-suc-zero i j refl = refl

  pinch-zero : {j : Fin (suc n)} → (i : Fin (suc n)) → i ≡ zero → pinch i (suc j) ≡ j
  pinch-zero i refl = refl

  inverse-zero : (p : Fin (suc n)) (ps : Permutation n) → ⟦ inverse (p :- ps) ⟧ p ≡ zero
  inverse-zero zero     ps  = refl
  inverse-zero {suc n} (suc p) ps =
    let p₀ = unzero ps in
    let ih = inverse-zero p (remove p₀ ps ) in
    skip-suc-zero p₀ _
      (trans (cong (λ □ → ⟦ inverse (pinch □ (suc p) :- remove p₀ ps) ⟧ p)
                   (unzero-correct ps))
             ih)

  -- Don't try writing this out in equational style
  --   the evaluation blows up in your face...
  remove-inverse : (p : Fin (suc n)) (ps : Permutation n) →
    remove p (inverse (p :- ps)) ≡ inverse ps
  remove-inverse zero ps = refl
  remove-inverse {n = suc _} (suc p) ps rewrite unzero-correct ps =
    let p₀ = unzero ps in
    let ps' = (p :- remove (unzero ps) ps) in
    let ih = remove-inverse p (remove p₀ ps) in
    cong₂ _:-_ (pinch-zero (⟦ unzero ps' :- inverse (remove (unzero ps') ps') ⟧ p)
               (inverse-zero p (remove p₀ ps))) ih

  inverse-prop₂ nil = refl
  inverse-prop₂ {n = suc _} (p :- ps) =
    inverse (p :- ps) ⊙ (p :- ps)
      ≡⟨ refl ⟩
    ⟦ inverse (p :- ps) ⟧ p :- remove p (inverse (p :- ps)) ⊙ ps
      ≡⟨ cong₂ _:-_ (inverse-zero p ps) (cong (_⊙ ps) (remove-inverse p ps)) ⟩
    zero :- inverse ps ⊙ ps
      ≡⟨ cong (zero :-_) (inverse-prop₂ ps) ⟩
    zero :- idₚ ∎
\end{code}

<<more-inverse-properties>>
\begin{code}
  inverse-unique      : (ps qs : Permutation n)  → ps ⊙ qs ≡ idₚ → qs ≡ inverse ps
  inverse-compose     : (ps qs : Permutation n)  → inverse qs ⊙ inverse ps ≡ inverse (ps ⊙ qs)
  inverse-inverse-id  : (ps : Permutation n)     → inverse (inverse ps) ≡ ps
\end{code}

\begin{code}
  inverse-unique ps qs ps⊙qs≡idₚ =
      qs
    ≡⟨ sym (compose-id₁ qs) ⟩
      idₚ ⊙ qs
    ≡⟨ cong (_⊙ qs) (sym (inverse-prop₂ ps)) ⟩
      (inverse ps ⊙ ps) ⊙ qs
    ≡⟨ compose-assoc (inverse ps) ps qs ⟩
      inverse ps ⊙ (ps ⊙ qs)
    ≡⟨ cong (inverse ps ⊙_) ps⊙qs≡idₚ ⟩
      inverse ps ⊙ idₚ
    ≡⟨ compose-id₂ (inverse ps) ⟩
      inverse ps ∎

  inverse-swaps : ∀ (ps qs : Permutation n) → ((ps ⊙ qs) ⊙ (inverse qs ⊙ inverse ps)) ≡ idₚ
  inverse-swaps ps qs =
       (ps ⊙ qs) ⊙ (inverse qs ⊙ inverse ps)
     ≡⟨ compose-assoc ps qs (inverse qs ⊙ inverse ps) ⟩
       ps ⊙ (qs ⊙ (inverse qs ⊙ inverse ps))
     ≡⟨ cong (ps ⊙_) (sym (compose-assoc qs (inverse qs) (inverse ps))) ⟩
       ps ⊙ ((qs ⊙ inverse qs) ⊙ inverse ps)
     ≡⟨ cong (λ □ → ps ⊙ (□ ⊙ inverse ps)) (inverse-prop₁ qs) ⟩
       ps ⊙ (idₚ ⊙ inverse ps)
     ≡⟨ cong (ps ⊙_) (compose-id₁ (inverse ps)) ⟩
       ps ⊙ inverse ps
     ≡⟨ inverse-prop₁ ps ⟩
       idₚ ∎

  inverse-compose ps qs = inverse-unique _ _ (inverse-swaps ps qs)

  inverse-inverse-id ps = sym (inverse-unique _ _ (inverse-prop₂ ps))
\end{code}

--------------------------------------------------------------------------------
                          --- Conjugation ---
--------------------------------------------------------------------------------

<<conjugation>>
\begin{code}
  conjugation : Permutation n → Permutation n → Permutation n
  conjugation g x = g ⊙ (x ⊙ inverse g)
\end{code}

∀ ps → (conjugation ps) is a functor from Permutation → Permutation

<<conjugation-properties>>
\begin{code}
  conjugation-id : conjugation (idₚ {n}) ≐ id
  conjugation-id ps =
      conjugation idₚ ps
    ≡⟨ refl ⟩
      idₚ ⊙ (ps ⊙ inverse idₚ)
    ≡⟨ compose-id₁ _ ⟩
      (ps ⊙ inverse idₚ)
    ≡⟨ cong (ps ⊙_) inverse-id ⟩
      (ps ⊙ idₚ)
    ≡⟨ compose-id₂ ps ⟩
      ps ∎

  conjugation-compose : (ps qs : Permutation n) →
    conjugation (ps ⊙ qs) ≐ (conjugation ps) ∘ (conjugation qs)
  conjugation-compose ps qs rs =
      conjugation (ps ⊙ qs) rs
    ≡⟨ refl  ⟩
      (ps ⊙ qs) ⊙ (rs ⊙ (inverse (ps ⊙ qs)))
    ≡⟨ cong (λ □ → (ps ⊙ qs) ⊙ (rs ⊙ □)) (sym (inverse-compose ps qs)) ⟩
      (ps ⊙ qs) ⊙ (rs ⊙ (inverse qs ⊙ inverse ps))
    ≡⟨ compose-assoc ps qs (rs ⊙ (inverse qs ⊙ inverse ps)) ⟩
      ps ⊙ (qs ⊙ (rs ⊙ (inverse qs ⊙ inverse ps)))
    ≡⟨ cong (λ □ → ps ⊙ (qs ⊙ □)) (sym (compose-assoc rs (inverse qs) (inverse ps))) ⟩
      ps ⊙ (qs ⊙ ((rs ⊙ inverse qs) ⊙ inverse ps))
    ≡⟨ cong (ps ⊙_) (sym (compose-assoc qs (rs ⊙ inverse qs) (inverse ps))) ⟩
      ps ⊙ ((qs ⊙ (rs ⊙ inverse qs)) ⊙ inverse ps)
    ≡⟨ refl ⟩
      ps ⊙ (conjugation qs rs ⊙ inverse ps)
    ≡⟨ refl ⟩
      conjugation ps (conjugation qs rs)
    ≡⟨ refl ⟩
      (conjugation ps ∘ conjugation qs) rs
    ∎
\end{code}

<<conjugation-preserves>>
\begin{code}
  conjugation-preserves-id : (ps : Permutation n) → conjugation ps idₚ ≡ idₚ
  conjugation-preserves-id ps =
       conjugation ps idₚ
     ≡⟨ refl ⟩
       ps ⊙ (idₚ ⊙ inverse ps)
     ≡⟨ cong (ps ⊙_) (compose-id₁ (inverse ps)) ⟩
       ps ⊙ inverse ps
     ≡⟨ inverse-prop₁ ps ⟩
       idₚ
     ∎

  conjugation-preserves-composition : (ps qs rs : Permutation n) →
      conjugation ps (qs ⊙ rs) ≡ conjugation ps qs ⊙ conjugation ps rs
  conjugation-preserves-composition ps qs rs =
      conjugation ps (qs ⊙ rs)
    ≡⟨ refl ⟩
      ps ⊙ ((qs ⊙ rs) ⊙ inverse ps)
    ≡⟨ cong (ps ⊙_) (compose-assoc qs rs (inverse ps)) ⟩
      ps ⊙ (qs ⊙ (rs ⊙ inverse ps))
    ≡⟨ sym (compose-assoc ps qs (rs ⊙ inverse ps)) ⟩
      (ps ⊙ qs) ⊙ (rs ⊙ inverse ps)
    ≡⟨ cong (λ □ → (ps ⊙ □) ⊙ (rs ⊙ inverse ps)) (sym (compose-id₂ qs)) ⟩
      (ps ⊙ (qs ⊙ idₚ)) ⊙ (rs ⊙ inverse ps)
    ≡⟨ cong (λ □ → (ps ⊙ (qs ⊙ □)) ⊙ (rs ⊙ inverse ps)) (sym (inverse-prop₂ ps)) ⟩
      (ps ⊙ (qs ⊙ (inverse ps ⊙ ps))) ⊙ (rs ⊙ inverse ps)
    ≡⟨ cong (λ □ → (ps ⊙ □) ⊙ (rs ⊙ inverse ps)) (sym (compose-assoc qs (inverse ps) ps)) ⟩
      (ps ⊙ ((qs ⊙ inverse ps) ⊙ ps)) ⊙ (rs ⊙ inverse ps)
    ≡⟨ cong (_⊙ (rs ⊙ inverse ps)) (sym (compose-assoc ps (qs ⊙ inverse ps) ps)) ⟩
      ((ps ⊙ (qs ⊙ inverse ps)) ⊙ ps) ⊙ (rs ⊙ inverse ps)
    ≡⟨ compose-assoc (ps ⊙ (qs ⊙ inverse ps)) ps (rs ⊙ inverse ps) ⟩
      (ps ⊙ (qs ⊙ inverse ps)) ⊙ (ps ⊙ (rs ⊙ inverse ps))
    ≡⟨ refl ⟩
      conjugation ps qs ⊙ conjugation ps rs
    ∎

  conjugation-preserves-inverse : (ps qs : Permutation n) →
    conjugation ps (inverse qs) ≡ inverse (conjugation ps qs)
  conjugation-preserves-inverse ps qs =
      conjugation ps (inverse qs)
    ≡⟨ refl ⟩
      ps ⊙ (inverse qs ⊙ inverse ps)
    ≡⟨ sym (compose-assoc ps (inverse qs) (inverse ps)) ⟩
      (ps ⊙ inverse qs) ⊙ inverse ps
    ≡⟨ cong (λ □ → (□ ⊙ inverse qs) ⊙ inverse ps) (sym (inverse-inverse-id ps)) ⟩
      (inverse (inverse ps) ⊙ inverse qs) ⊙ inverse ps
    ≡⟨ cong (_⊙ inverse ps) (inverse-compose qs (inverse ps)) ⟩
      inverse (qs ⊙ inverse ps) ⊙ inverse ps
    ≡⟨ inverse-compose ps (qs ⊙ inverse ps) ⟩
      inverse (ps ⊙ (qs ⊙ inverse ps))
    ≡⟨ refl ⟩
      inverse (conjugation ps qs)
    ∎
\end{code}

--------------------------------------------------------------------------------
         --- Vector utilities - towards decision procedure ---
--------------------------------------------------------------------------------

\begin{code}
module Utils where
  -- A few helper functions on vectors, some of which are already in
  -- Data.Vec in some form or another

  data All (P : A → Set) : Vec A n → Set where
    nil : All P []
    _∷_ : {x : A} {xs : Vec A n} → P x  → All P xs → All P (x ∷ xs)

  -- Flipped Data.Vec.insertAt
  insert : Fin (suc n) → A → Vec A n → Vec A (suc n)
  insert zero    x ys       = x ∷ ys
  insert (suc i) x (y ∷ ys) = y ∷ insert i x ys

  -- Flipped Data.Vec.removeAt
  remove : Fin (suc n) → Vec A (suc n) → Vec A n
  remove             zero    (_ ∷ xs) = xs
  remove {n = suc _} (suc i) (x ∷ xs) = x ∷ remove i xs

  -- Properties
  lookup-insert :  (i : Fin (suc n)) (x : A) (xs : Vec A n) →
                   lookup (insert i x xs) i ≡ x
  lookup-insert zero     x  xs        = refl
  lookup-insert (suc i)  x  (y ∷ xs)  = lookup-insert i x xs

  remove-insert : {y : A} (i : Fin (suc n)) (xs : Vec A n) → remove i (insert i y xs) ≡ xs
  remove-insert zero    xs       = refl
  remove-insert (suc i) (x ∷ xs) = cong (x ∷_) (remove-insert i xs)

  remove-lookup :  (i : Fin (suc n)) (xs : Vec A (suc n)) →
                   lookup (remove i xs) ≐ lookup xs ∘ Permutations.skip i
  remove-lookup zero     (x ∷ xs) j        = refl
  remove-lookup (suc i)  (x ∷ xs) zero     = refl
  remove-lookup (suc i)  (x ∷ xs) (suc j)  = remove-lookup i xs j

  insert-remove : ∀ (j : Fin (suc n)) (zs : Vec A (suc n)) →
                  insert j (lookup zs j) (remove j zs) ≡ zs
  insert-remove {n}      zero     (z ∷ zs) = refl
  insert-remove {suc n}  (suc j)  (z ∷ zs) = cong (z ∷_) (insert-remove j zs)

  -- Extensional equality for Vec
  vec-eq : {A : Set} {n : ℕ} {xs ys : Vec A n} → (lookup xs ≐ lookup ys) → xs ≡ ys
  vec-eq {xs = []}     {ys = []}     eq = refl
  vec-eq {xs = x ∷ xs} {ys = y ∷ ys} eq = cong₂ _∷_ (eq zero) (vec-eq (eq ∘ suc))

  -- Using vec-eq, we don't need to shift indices inside tabulate.
  -- We just evaluate both sides at an arbitrary index `i`.
  tabulate-compose : {A : Set} {n : ℕ} (f g : Fin n → Fin n) (xs : Vec A n) →
    tabulate (lookup (tabulate (lookup xs ∘ f)) ∘ g)
    ≡ tabulate (lookup xs ∘ (f ∘ g))
  tabulate-compose f g xs = vec-eq (λ i →
    begin
      lookup (tabulate (lookup (tabulate (lookup xs ∘ f)) ∘ g)) i
    ≡⟨ lookup∘tabulate _ i ⟩
      lookup (tabulate (lookup xs ∘ f)) (g i)
    ≡⟨ lookup∘tabulate (lookup xs ∘ f) (g i) ⟩
      (lookup xs ∘ f) (g i)
    ≡⟨ sym (lookup∘tabulate _ i) ⟩
      lookup (tabulate (lookup xs ∘ (f ∘ g))) i
    ∎)

\end{code}

And now we move on to the decision procedure that finds a permutation between any
two vectors (or proves that no such permuation exists)

\begin{code}
module decide-permute (A : Set) (_≟_ : (x y : A) → Dec (x ≡ y)) where
  open Permutations
    using (Permutation; nil; _:-_ ;⟦_⟧;
           idₚ; _⊙_; inverse;
           idₚ-is-id; inverse-prop₁; compose-correct)
  open Utils
    using (All; nil; _∷_;
           insert; remove; insert-remove; remove-insert; remove-lookup; lookup-insert;
           tabulate-compose)

  variable
    xs ys zs : Vec A n
    x y : A
    i : Fin n
\end{code}
  --------------------------------------------------------------------------------
              --- The action of permutation on vectors ---
  --------------------------------------------------------------------------------

  -- The action can be defined via the semantics:
<<permute-vec-spec>>
\begin{code}
  permute-vec-spec : Permutation n → Vec A n → Vec A n
  permute-vec-spec p xs = tabulate (lookup xs ∘ ⟦ p ⟧)
\end{code}
But also by inductively on the Lehmer code:
  permute-vec : Permutation n → Vec A n → Vec A n
this is used to prove the properties of composition and inverse.

<<vec-semantics>>
\begin{code}
  ⟦_⟧v : (p : Permutation n) → Vec A n → Vec A n
  ⟦ nil ⟧v      []   = []
  ⟦ i :- ps ⟧v  xs   = lookup xs i ∷ ⟦ ps ⟧v (remove i xs)
\end{code}
We define the vector action explicitly as a right action:
<<vec-right-action>>
\begin{code}
  infixl 5 _◁_

  _◁_ : Vec A n → Permutation n → Vec A n
  xs ◁ p = ⟦ p ⟧v xs
\end{code}

The correctness proof connecting the structural and semantic definitions
<<vec-semantics-spec>>
\begin{code}
  ⟦_⟧v-correct : (p : Permutation n) → ∀ xs → ⟦ p ⟧v xs ≡ tabulate (lookup xs ∘ ⟦ p ⟧)
\end{code}

\begin{code}
  ⟦_⟧v-correct nil [] = refl
  ⟦_⟧v-correct (i :- ps) xs =
       lookup xs i ∷ ⟦ ps ⟧v (remove i xs)
     ≡⟨ cong (_ ∷_) (⟦ ps ⟧v-correct (remove i xs)) ⟩
        lookup xs i ∷ tabulate (lookup (remove i xs) ∘ ⟦ ps ⟧)
     ≡⟨ cong (_ ∷_) (tabulate-cong (λ j → remove-lookup i xs (⟦ ps ⟧ j))) ⟩
       (lookup xs i ∷ tabulate (λ j → lookup xs (Permutations.skip i (⟦ ps ⟧ j))))
     ≡⟨⟩
       permute-vec-spec (i :- ps) xs
     ∎
\end{code}

The right action composition law looks like associativity: "xs after (p after q)" equals "(xs after p) after q".
<<triangle-compose>>
\begin{code}
  ◁-compose : (p q : Permutation n) (xs : Vec A n)  → xs ◁ (p ⊙ q) ≡ (xs ◁ p) ◁ q
  ◁-compose p q xs =
      xs ◁ (p ⊙ q)
    ≡⟨ ⟦ p ⊙ q ⟧v-correct xs ⟩
      tabulate (lookup xs ∘ ⟦ p ⊙ q ⟧)
    ≡⟨ tabulate-cong (λ i → cong (lookup xs) (sym (compose-correct p q i))) ⟩
      tabulate (lookup xs ∘ ⟦ p ⟧ ∘ ⟦ q ⟧)
    ≡⟨ sym (tabulate-compose ⟦ p ⟧ ⟦ q ⟧ xs) ⟩
      tabulate (lookup (tabulate (lookup xs ∘ ⟦ p ⟧)) ∘ ⟦ q ⟧)
    ≡⟨ sym (⟦ q ⟧v-correct (tabulate (lookup xs ∘ ⟦ p ⟧))) ⟩
      ⟦ q ⟧v (tabulate (lookup xs ∘ ⟦ p ⟧))
    ≡⟨ cong ⟦ q ⟧v (sym (⟦ p ⟧v-correct xs)) ⟩
      (xs ◁ p) ◁ q
    ∎
\end{code}

<<triangle-compose>>
\begin{code}
  vec-compose : (p q : Permutation n) (xs : Vec A n)  → ⟦ p ⊙ q ⟧v xs ≡ ⟦ q ⟧v (⟦ p ⟧v xs)
  vec-compose p q xs =
      xs ◁ (p ⊙ q)
    ≡⟨ ⟦ p ⊙ q ⟧v-correct xs ⟩
      tabulate (lookup xs ∘ ⟦ p ⊙ q ⟧)
    ≡⟨ tabulate-cong (λ i → cong (lookup xs) (sym (compose-correct p q i))) ⟩
      tabulate (lookup xs ∘ ⟦ p ⟧ ∘ ⟦ q ⟧)
    ≡⟨ sym (tabulate-compose ⟦ p ⟧ ⟦ q ⟧ xs) ⟩
      tabulate (lookup (tabulate (lookup xs ∘ ⟦ p ⟧)) ∘ ⟦ q ⟧)
    ≡⟨ sym (⟦ q ⟧v-correct (tabulate (lookup xs ∘ ⟦ p ⟧))) ⟩
      ⟦ q ⟧v (tabulate (lookup xs ∘ ⟦ p ⟧))
    ≡⟨ cong ⟦ q ⟧v (sym (⟦ p ⟧v-correct xs)) ⟩
      (xs ◁ p) ◁ q
    ∎
\end{code}


<<permute-vec-props>>
\begin{code}
  permute-vec-id : (xs : Vec A n) → ⟦ idₚ ⟧v xs ≡ xs
  permute-vec-inverse : (p : Permutation n) →
    ⟦ inverse p ⟧v  ∘ ⟦ p ⟧v  ≐  id
  permute-vec-compose : (p₀ p₁ : Permutation n) →
    ⟦ p₀ ⊙ p₁ ⟧v ≐ ⟦ p₁ ⟧v ∘ ⟦ p₀ ⟧v
\end{code}

\begin{code}
  permute-vec-id [] = refl
  permute-vec-id (x ∷ xs) = cong (x ∷_) (permute-vec-id xs)

  permute-vec-inverse p xs =
      ⟦ inverse p ⟧v (⟦ p ⟧v xs)
    ≡⟨ cong ⟦ inverse p ⟧v (⟦ p ⟧v-correct xs) ⟩
      ⟦ inverse p ⟧v (tabulate (lookup xs ∘ ⟦ p ⟧))
    ≡⟨ ⟦ inverse p ⟧v-correct _ ⟩
      tabulate (lookup (tabulate (lookup xs ∘ ⟦ p ⟧)) ∘ ⟦ inverse p ⟧)
    ≡⟨ tabulate-compose ⟦ p ⟧ ⟦ inverse p ⟧ xs ⟩
      tabulate (lookup xs ∘ ⟦ p ⟧ ∘ ⟦ inverse p ⟧)
    ≡⟨ tabulate-cong (λ i → cong (lookup xs) (compose-correct p (inverse p) i )) ⟩
      tabulate (lookup xs ∘ ⟦ p ⊙ inverse p ⟧)
    ≡⟨ tabulate-cong (λ i → cong (lookup xs) (cong (λ □ → ⟦ □ ⟧ i) (inverse-prop₁ p))) ⟩
      tabulate (lookup xs ∘ ⟦ idₚ ⟧)
    ≡⟨ tabulate-cong (λ i → cong (lookup xs) (idₚ-is-id i)) ⟩
      tabulate (lookup xs ∘ id)
    ≡⟨⟩
      tabulate (lookup xs)
    ≡⟨ Data.Vec.Properties.tabulate∘lookup xs ⟩
      xs
    ∎

  permute-vec-compose = ◁-compose
\end{code}

  --------------------------------------------------------------------------------
                     --- The Permutes relation ---
  --------------------------------------------------------------------------------

  -- The Permutes relation between vectors is an equivalence relation
<<Permutes>>
\begin{code}
  data Permutes (xs : Vec A n) : Vec A n → Set where
    ⟨_⟩ : (p : Permutation n) → Permutes xs (⟦ p ⟧v xs)
\end{code}

\begin{code}
  coerce : {xs ys zs : Vec A n} → ys ≡ zs → Permutes xs ys → Permutes xs zs
  coerce refl p = p

  permutes-trans : {xs ys zs : Vec A n} → Permutes xs ys → Permutes ys zs → Permutes xs zs
  permutes-trans {xs = xs} ⟨ p₀ ⟩ ⟨ p₁ ⟩ = coerce (permute-vec-compose p₀ p₁ xs) ⟨ p₀ ⊙ p₁ ⟩

  permutes-sym : {xs ys : Vec A n} → Permutes xs ys → Permutes ys xs
  permutes-sym {xs = xs} ⟨ p ⟩ = coerce (permute-vec-inverse p xs) ⟨ inverse p ⟩

  permutes-refl : {xs : Vec A n} → Permutes xs xs
  permutes-refl {xs = xs} = coerce (permute-vec-id xs) ⟨ idₚ ⟩
\end{code}

<<permutes-insert-inv>>
\begin{code}
  permutes-insert-inv : {i : Fin (suc n)} → Permutes (insert i y ys) (y ∷ ys)
  permutes-insert-inv {y = y} {ys} {i} =
    coerce (
          (insert i y ys) ◁ (i :- idₚ)
        ≡⟨⟩
          lookup (insert i y ys) i  ∷  (remove i (insert i y ys) ◁ idₚ)
        ≡⟨ cong (λ □ → lookup (insert i y ys) i ∷ (□ ◁ idₚ)) (remove-insert i ys) ⟩
          lookup (insert i y ys) i ∷ (ys ◁ idₚ)
        ≡⟨ cong₂ _∷_ (lookup-insert i y ys) (permute-vec-id ys) ⟩
          y ∷ ys ∎ )
    ⟨ i :- idₚ ⟩
\end{code}

\begin{code}
  permutes-insert-to : Permutes (x ∷ xs) (insert i x xs)
  permutes-insert-to = permutes-sym permutes-insert-inv
\end{code}


<<permutes-tail>>
\begin{code}
  permutes-tail : Permutes (x ∷ xs) (x ∷ ys) → Permutes xs ys
\end{code}
\begin{code}
  -- Implementation of permutes-tail
  permutes-remove : (i : Fin (suc n)) → lookup (x ∷ xs) i ≡ x →
    Permutes xs (remove i (x ∷ xs))
  permutes-remove zero eq = permutes-refl
  permutes-remove {suc n} {x = x} {xs = xs} (suc i) refl =
    coerce (cong (x ∷_) (permute-vec-id (remove i xs))) ⟨ i :- idₚ ⟩

  permutes-tail p = permutes-tail-aux p refl
    where
    step :  (i : Fin (suc n)) → (p : Permutation n) →
            lookup (x ∷ xs) i ≡ x  →  (remove i (x ∷ xs) ◁ p) ≡ ys →
            Permutes xs ys
    step {x = x} {xs = xs} {ys = ys} i p eq-lookup refl =
      permutes-trans (permutes-remove i eq-lookup) ⟨ p ⟩

    permutes-tail-aux : Permutes (x ∷ xs) zs → zs ≡ x ∷ ys → Permutes xs ys
    permutes-tail-aux {x = x} {xs = xs} {ys = ys} ⟨ i :- p ⟩ eq =
      step i p (∷-inj-head eq) (∷-inj-tail eq)
\end{code}

<<permutes-preserves>>
\begin{code}
  permutes-preserves : All (x ≢_) ys → Permutes (x ∷ xs) ys → ⊥
\end{code}

Searching for a given element in a vector

<<Find>>
\begin{code}
  data Find : A → Vec A n → Set where
    somewhere  : (ys : Vec A n) (i : Fin (suc n)) → Find x (insert i x ys)
    nowhere    : All (x ≢_) xs → Find x xs
\end{code}

<<find-type>>
\begin{code}
  find : (x : A) → (xs : Vec A n) → Find x xs
\end{code}

<<find-def>>
\begin{code}
  find x [] = nowhere nil
  find x (y ∷ ys)  with x ≟ y
  find {n = n} x (.x ∷ ys) | yes refl = somewhere ys zero
  find {n = n} x (y ∷ ys)  | no neq with find x ys
  find {n = n} x (y ∷ ys)  | no neq | somewhere zs i = somewhere (y ∷ zs) (suc i)
  find {n = n} x (y ∷ ys)  | no neq | nowhere neqs = nowhere (neq ∷ neqs)
\end{code}

\begin{code}
  lookup-not-in : All (λ y → x ≢ y) xs → (i : Fin n) → (x ≡ lookup xs i) → ⊥
  lookup-not-in (neq ∷ neqs) zero refl = neq refl
  lookup-not-in (neq ∷ neqs) (suc i) eq  = lookup-not-in neqs i eq
\end{code}

Helper lemmas relating permutations and All
\begin{code}
  lookup-all : {P : A → Set} → (i : Fin n) → All P xs → P (lookup xs i)
  lookup-all zero    (px ∷ pxs) = px
  lookup-all (suc i) (px ∷ pxs) = lookup-all i pxs

  remove-all : {P : A → Set} → (i : Fin (suc n)) → All P xs → All P (remove i xs)
  remove-all zero    (_  ∷ pxs)         = pxs
  remove-all {suc n} (suc i) (px ∷ pxs) = px ∷ remove-all i pxs

  permutes-all : {P : A → Set} → Permutes xs ys → All P xs → All P ys
  permutes-all ⟨ nil ⟩ nil    = nil
  permutes-all ⟨ i :- p ⟩ pxs = lookup-all i pxs ∷ permutes-all ⟨ p ⟩ (remove-all i pxs)

  head-all : {P : A → Set} → All P (x ∷ xs) → P x
  head-all (px ∷ _) = px

  permutes-preserves {x} {xs} neqs p = head-all (permutes-all (permutes-sym p) neqs) refl
\end{code}

<<permutes-insert>>
\begin{code}
  permutes-insert : Permutes (x ∷ xs) (insert i x ys) ⇔ Permutes xs ys
\end{code}

\begin{code}
  permutes∷ : Permutes xs ys → Permutes (x ∷ xs) (insert i x ys)
  permutes∷ ⟨ p ⟩ = permutes-trans ⟨ (zero :- p) ⟩ permutes-insert-to

  permutes-insert-tail : Permutes (x ∷ xs) (insert i x ys) → Permutes xs ys
  permutes-insert-tail p =
    permutes-tail (permutes-trans p (permutes-sym permutes-insert-to))

  permutes-insert = Function.mk⇔ permutes-insert-tail permutes∷
  open Equivalence using (to; from)
\end{code}

<<decide>>
\begin{code}
  decide : (xs ys : Vec A n) → Dec (Permutes xs ys)
  decide []        []  = yes ⟨ nil ⟩
  decide (x ∷ xs)  ys  with find x ys
  ... | nowhere x̸∈ys = no (permutes-preserves x̸∈ys)
  ... | somewhere zs i  with decide xs zs
  ... | yes p       = yes (from permutes-insert p)
  ... | no  q       = no (q ∘ to permutes-insert)
\end{code}

\begin{code}
open import Data.Vec using (lookup)
\end{code}


\begin{code}
open import Data.Vec using (tabulate)
open Permutations using (Permutation; _:-_; nil; pinch; inverse)
pinch-examples : Vec (Fin 4) 5
pinch-examples = tabulate (pinch {4} (suc (suc zero)))

example : Permutation 4
example = suc zero :- suc zero :- suc zero :- zero :- nil

inverse-example : inverse example ≡ suc (suc (suc zero)) :- zero :- zero :- zero :- nil
inverse-example = refl
\end{code}

We check that our inductive Lehmer-code representation (|p :- ps| meaning
"the permutation maps 0 to p") agrees with the classical (Wikipedia)
inversion-count definition of the Lehmer code, for all permutations
(values of |Permutation n|).

\begin{code}
module CheckLehmerInversionCount where
  open import Data.Fin using (toℕ; _<_)
  open import Data.Fin.Properties using (_<?_)
  open import Data.Nat.Base using (s<s; s<s⁻¹; z<s)
  open import Data.Nat.Properties using (+-suc; <-irrefl; n≮0)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open Permutations using (⟦_⟧; skip)

  -- Helper: count how many elements of Fin n satisfy a decidable predicate.
  countDec : {n : ℕ} (P : Fin n → Set) (dec : ∀ i → Dec (P i)) → ℕ
  countDec {zero}  P dec = 0
  countDec {suc n} P dec with dec zero
  ... | yes _ = suc (countDec (P ∘ suc) (dec ∘ suc))
  ... | no  _ = countDec (P ∘ suc) (dec ∘ suc)

  countYes : {A : Set} → Dec A → ℕ
  countYes (yes _) = 1
  countYes (no  _) = 0

  -- countDec is invariant under swapping a predicate for a logically
  -- equivalent one (with possibly different Dec witnesses).
  countDec-≐ : {n : ℕ} {P Q : Fin n → Set}
    (decP : ∀ i → Dec (P i)) (decQ : ∀ i → Dec (Q i)) →
    (∀ i → P i → Q i) → (∀ i → Q i → P i) → countDec P decP ≡ countDec Q decQ
  countDec-≐ {zero}  decP decQ P⇒Q Q⇒P = refl
  countDec-≐ {suc n} decP decQ P⇒Q Q⇒P with decP zero | decQ zero
  ... | yes p | yes q = cong suc (countDec-≐ (decP ∘ suc) (decQ ∘ suc) (P⇒Q ∘ suc) (Q⇒P ∘ suc))
  ... | yes p | no ¬q = ⊥-elim (¬q (P⇒Q zero p))
  ... | no ¬p | yes q = ⊥-elim (¬p (Q⇒P zero q))
  ... | no ¬p | no ¬q = countDec-≐ (decP ∘ suc) (decQ ∘ suc) (P⇒Q ∘ suc) (Q⇒P ∘ suc)

  -- Removing a specific pivot from the counted domain: counting over
  -- Fin (suc m) splits into "does the pivot itself count" plus counting
  -- over the rest, reindexed in via `skip`.
  countDec-skip : {m : ℕ} (p : Fin (suc m)) (P : Fin (suc m) → Set) (dec : ∀ j → Dec (P j)) →
    countDec P dec ≡ countYes (dec p) + countDec (P ∘ skip p) (dec ∘ skip p)
  countDec-skip zero P dec with dec zero
  ... | yes _ = refl
  ... | no  _ = refl
  countDec-skip {suc m} (suc p) P dec with dec zero
  ... | yes _ = trans (cong suc (countDec-skip p (P ∘ suc) (dec ∘ suc)))
                       (sym (+-suc (countYes (dec (suc p))) _))
  ... | no  _ = countDec-skip p (P ∘ suc) (dec ∘ suc)

  -- countDec is invariant under reindexing by a permutation's semantics.
  count-reindex : {m : ℕ} (qs : Permutation m) (P : Fin m → Set) (dec : ∀ k → Dec (P k)) →
    countDec (P ∘ ⟦ qs ⟧) (dec ∘ ⟦ qs ⟧) ≡ countDec P dec
  count-reindex nil P dec = refl
  count-reindex (q :- qs) P dec rewrite countDec-skip q P dec with dec q
  ... | yes _ = cong suc (count-reindex qs (P ∘ skip q) (dec ∘ skip q))
  ... | no  _ = count-reindex qs (P ∘ skip q) (dec ∘ skip q)

  -- If nothing satisfies P, the count is 0.
  countDec-false : {n : ℕ} {P : Fin n → Set} (dec : ∀ i → Dec (P i)) → (∀ i → ¬ P i) → countDec P dec ≡ 0
  countDec-false {zero}  dec ¬P = refl
  countDec-false {suc n} dec ¬P with dec zero
  ... | yes p = ⊥-elim (¬P zero p)
  ... | no  _ = countDec-false (dec ∘ suc) (¬P ∘ suc)

  -- The number of elements of Fin (suc m) below a given p is toℕ p.
  count-below : {m : ℕ} (p : Fin (suc m)) →
    countDec {suc m} (_< p) (_<? p) ≡ toℕ p
  count-below {m} zero = countDec-false {suc m} (_<? Data.Fin.zero {m}) (λ k ())
  count-below {suc m} (suc p) with Data.Fin.zero {suc m} <? suc p
  ... | no ¬p = ⊥-elim (¬p z<s)
  ... | yes _ = cong suc (trans
      (countDec-≐ {suc m} (λ (k : Fin (suc m)) → suc k <? suc p) (_<? p)
                          (λ k → s<s⁻¹) (λ k → s<s))
      (count-below p))

  -- skip preserves and reflects strict order.
  skip-mono-< : {m : ℕ} (p : Fin (suc m)) (a b : Fin m) → a < b → skip p a < skip p b
  skip-mono-< zero     a       b       a<b = s<s a<b
  skip-mono-< (suc p)  zero    zero    ()
  skip-mono-< (suc p)  zero    (suc b) _   = z<s
  skip-mono-< (suc p)  (suc a) zero    ()
  skip-mono-< (suc p)  (suc a) (suc b) (s<s a<b) = s<s (skip-mono-< p a b a<b)

  skip-cancel-< : {m : ℕ} (p : Fin (suc m)) (a b : Fin m) → skip p a < skip p b → a < b
  skip-cancel-< zero     a       b       (s<s a<b) = a<b
  skip-cancel-< (suc p)  zero    zero    ()
  skip-cancel-< (suc p)  zero    (suc b) _   = z<s
  skip-cancel-< (suc p)  (suc a) zero    ()
  skip-cancel-< (suc p)  (suc a) (suc b) (s<s a<b) = s<s (skip-cancel-< p a b a<b)

  -- If a proposition is false, countYes of its Dec instance is 0.
  countYes-no : {A : Set} (d : Dec A) → ¬ A → countYes d ≡ 0
  countYes-no (yes a) ¬a = ⊥-elim (¬a a)
  countYes-no (no  _) ¬a = refl

  -- Wikipedia's inversion-count Lehmer code, over an arbitrary semantic function:
  -- L(f)_i = #{ j > i : f(j) < f(i) }
  lehmer-pred : {n : ℕ} (f : Fin n → Fin n) (i j : Fin n) → Set
  lehmer-pred f i j = (i < j) × (f j < f i)

  lehmer-dec : {n : ℕ} (f : Fin n → Fin n) (i j : Fin n) → Dec (lehmer-pred f i j)
  lehmer-dec f i j with i <? j | f j <? f i
  ... | yes p₁ | yes p₂ = yes (p₁ , p₂)
  ... | yes p₁ | no ¬p₂ = no (λ z → ¬p₂ (proj₂ z))
  ... | no ¬p₁ | yes p₂ = no (λ z → ¬p₁ (proj₁ z))
  ... | no ¬p₁ | no ¬p₂ = no (λ z → ¬p₁ (proj₁ z))

  wikiLehmerAt : {n : ℕ} (f : Fin n → Fin n) (i : Fin n) → ℕ
  wikiLehmerAt f i = countDec (lehmer-pred f i) (lehmer-dec f i)

  wikiLehmerVec : {n : ℕ} (f : Fin n → Fin n) → Vec ℕ n
  wikiLehmerVec f = tabulate (wikiLehmerAt f)

  -- Extracting our inductive pivots as a vector of natural numbers.
  pivotNats : {n : ℕ} → Permutation n → Vec ℕ n
  pivotNats nil = []
  pivotNats (p :- ps) = toℕ p ∷ pivotNats ps

  -- The head of the Lehmer code is the head pivot's own value.
  lehmer-head : {m : ℕ} (p : Fin (suc m)) (ps : Permutation m) →
    wikiLehmerAt ⟦ p :- ps ⟧ zero ≡ toℕ p
  lehmer-head {m} p ps =
    begin
      countDec P₀ decP₀
    ≡⟨ countDec-skip zero P₀ decP₀ ⟩
      countYes (decP₀ zero) + countDec (P₀ ∘ skip zero) (decP₀ ∘ skip zero)
    ≡⟨ cong (_+ countDec (P₀ ∘ skip zero) (decP₀ ∘ skip zero))
            (countYes-no (decP₀ zero) (λ pr → <-irrefl refl (proj₁ pr))) ⟩
      countDec (P₀ ∘ skip zero) (decP₀ ∘ skip zero)
    ≡⟨ countDec-≐ (decP₀ ∘ skip zero) (λ i → skip p (⟦ ps ⟧ i) <? p)
                  (λ i pr → proj₂ pr) (λ i q → z<s , q) ⟩
      countDec (λ i → skip p (⟦ ps ⟧ i) < p) (λ i → skip p (⟦ ps ⟧ i) <? p)
    ≡⟨ count-reindex ps (LTp ∘ skip p) (decLTp ∘ skip p) ⟩
      countDec (LTp ∘ skip p) (decLTp ∘ skip p)
    ≡⟨ sym (cong (_+ countDec (LTp ∘ skip p) (decLTp ∘ skip p))
                 (countYes-no (decLTp p) (λ pf → <-irrefl refl pf))) ⟩
      countYes (decLTp p) + countDec (LTp ∘ skip p) (decLTp ∘ skip p)
    ≡⟨ sym (countDec-skip p LTp decLTp) ⟩
      countDec LTp decLTp
    ≡⟨ count-below p ⟩
      toℕ p
    ∎
    where
    f = ⟦ p :- ps ⟧

    P₀ : Fin (suc m) → Set
    P₀ = lehmer-pred f zero

    decP₀ : ∀ j → Dec (P₀ j)
    decP₀ = lehmer-dec f zero

    LTp : Fin (suc m) → Set
    LTp = _< p
    decLTp : ∀ k → Dec (LTp k)
    decLTp = _<? p

  -- The rest of the Lehmer code is the tail permutation's own Lehmer code.
  lehmer-tail : {m : ℕ} (p : Fin (suc m)) (ps : Permutation m) (i : Fin m) →
    wikiLehmerAt ⟦ p :- ps ⟧ (suc i) ≡ wikiLehmerAt ⟦ ps ⟧ i
  lehmer-tail {m} p ps i =
    begin
      countDec Pᵢ decPᵢ
    ≡⟨ countDec-skip zero Pᵢ decPᵢ ⟩
      countYes (decPᵢ zero) + countDec (Pᵢ ∘ suc) (decPᵢ ∘ suc)
    ≡⟨ cong (_+ countDec (Pᵢ ∘ suc) (decPᵢ ∘ suc)) (countYes-no (decPᵢ zero) (λ pr → n≮0 (proj₁ pr))) ⟩
      countDec (Pᵢ ∘ suc) (decPᵢ ∘ suc)
    ≡⟨ countDec-≐ (decPᵢ ∘ suc) (lehmer-dec ⟦ ps ⟧ i)
                  (λ i' pr → s<s⁻¹ (proj₁ pr) , skip-cancel-< p (⟦ ps ⟧ i') (⟦ ps ⟧ i) (proj₂ pr))
                  (λ i' pr → s<s (proj₁ pr) , skip-mono-< p (⟦ ps ⟧ i') (⟦ ps ⟧ i) (proj₂ pr)) ⟩
      wikiLehmerAt ⟦ ps ⟧ i
    ∎
    where
    f = ⟦ p :- ps ⟧

    Pᵢ : Fin (suc m) → Set
    Pᵢ = lehmer-pred f (suc i)

    decPᵢ : ∀ j → Dec (Pᵢ j)
    decPᵢ = lehmer-dec f (suc i)

  -- The main property: our inductive encoding produces exactly the
  -- sequence of Wikipedia inversion counts, for any actual permutation.
  lehmer-equivalence-prop : {n : ℕ} (ps : Permutation n) →
    pivotNats ps ≡ wikiLehmerVec ⟦ ps ⟧
  lehmer-equivalence-prop nil = refl
  lehmer-equivalence-prop (p :- ps) =
    begin
      toℕ p ∷ pivotNats ps
    ≡⟨ cong (toℕ p ∷_) (lehmer-equivalence-prop ps) ⟩
      toℕ p ∷ tabulate (wikiLehmerAt ⟦ ps ⟧)
    ≡⟨ cong (toℕ p ∷_) (tabulate-cong (λ i → sym (lehmer-tail p ps i))) ⟩
      toℕ p ∷ tabulate (λ i → wikiLehmerAt ⟦ p :- ps ⟧ (suc i))
    ≡⟨ cong (_∷ tabulate (λ i → wikiLehmerAt ⟦ p :- ps ⟧ (suc i))) (sym (lehmer-head p ps)) ⟩
      tabulate (wikiLehmerAt ⟦ p :- ps ⟧)
    ∎
\end{code}


\begin{code}
-- tabulating a function Fin n → Fin m
variable
  m : ℕ
\end{code}

<<table>>
\begin{code}
data Table : ℕ → ℕ → Set where
  nil  : Table zero m
  _∷_  : Fin (suc m) → Table n m → Table (suc n) (suc m)
\end{code}

\begin{code}
⟦_⟧t : Table n m → Fin n → Fin m
⟦ j ∷ _ ⟧t zero = j
⟦ j ∷ t ⟧t (suc i) = Permutations.skip j (⟦ t ⟧t i)

open import Data.Nat using (_≤_; s≤s; z≤n)

skip-skips : (j : Fin (suc n)) (i : Fin n) → Permutations.skip j i ≡ j → ⊥
skip-skips zero i ()
skip-skips (suc j) zero ()
skip-skips (suc j) (suc i) = skip-skips j i ∘ suc-inj

injective-table : n ≤ m → (t : Table n m) → ∀ i j → (⟦ t ⟧t i) ≡ (⟦ t ⟧t j) → i ≡ j
injective-table lt t zero zero eq = refl
injective-table lt (t ∷ ts) zero (suc j) eq = ⊥-elim (skip-skips t _ (sym eq))
injective-table lt (t ∷ ts) (suc i) zero eq = ⊥-elim (skip-skips t _ eq)
injective-table (s≤s lt) (t ∷ ts) (suc i) (suc j) eq =
  let ih = injective-table lt ts i j (Permutations.skip-inj t eq) in
  cong suc ih

open import Data.Product using (Σ; _,_)

data Skipped : Fin n → Fin n → Set where
  equal : (i : Fin n) → Skipped i i
  in-img : (i : Fin (suc n)) (j : Fin n) → Skipped i (Permutations.skip i j)

dec-skipped : (i j : Fin n) → Skipped i j
dec-skipped zero zero = equal zero
dec-skipped zero (suc j) = in-img zero j
dec-skipped (suc {suc n} i) zero = in-img (suc i) zero
dec-skipped (suc i) (suc j) with dec-skipped i j
... | equal k = equal (suc k)
... | in-img i' j' = in-img (suc i') (suc j')

-- Interesting inductive argument: do induction on *m* and invert the skip at the front if necessary.
surjective-table : (m : ℕ) → m ≤ n → (t : Table n m) → ∀ j → Σ (Fin n) (λ i → ⟦ t ⟧t i ≡ j)
surjective-table (suc m) (s≤s lt) (x ∷ ts) j with dec-skipped x j
... | equal i      = zero , refl
... | in-img i' j' = let (x , eq) = surjective-table m lt ts j'
                     in (suc x , cong (Permutations.skip _) eq)
\end{code}

surjective-table's hypothesis (m ≤ n) is never actually exercised when m < n
strictly: every inhabitant of Table n m witnesses n ≤ m, so Table n m is empty
whenever n > m.
\begin{code}
module TableSizeBound where
  open import Data.Nat using (_>_)
  open import Data.Nat.Properties using (≤-trans; 1+n≰n)

  table-index-≤ : Table n m → n ≤ m
  table-index-≤ nil     = z≤n
  table-index-≤ (_ ∷ t) = s≤s (table-index-≤ t)

  table-empty-when-> : n > m → Table n m → ⊥
  table-empty-when-> n>m t = 1+n≰n (≤-trans n>m (table-index-≤ t))
\end{code}

On the other hand, |injective-table| is not just sound but complete: every injective
function |Fin n -> Fin m| (with |n <= m|) arises from some |Table n m|, not
just some subclass of them.
\begin{code}
module TableCompleteness where
  open import Data.Fin using (punchOut)
  open import Data.Product using (proj₁; proj₂)

  Injective : {n m : ℕ} → (Fin n → Fin m) → Set
  Injective f = ∀ {i j} → f i ≡ f j → i ≡ j

  zero≢suc : {i : Fin n} → zero ≡ suc i → ⊥
  zero≢suc ()

  -- Same clauses as Data.Fin.Properties.punchIn-punchOut
  skip-punchOut : {i j : Fin (suc n)} (i≢j : i ≢ j) → Permutations.skip i (punchOut i≢j) ≡ j
  skip-punchOut              {i = zero}   {zero}   0≢0  = ⊥-elim (0≢0 refl)
  skip-punchOut              {i = zero}   {suc j}  _    = refl
  skip-punchOut {n = suc n}  {i = suc i}  {zero}   _    = refl
  skip-punchOut {n = suc n}  {i = suc i}  {suc j}  i≢j  = cong suc (skip-punchOut (i≢j ∘ cong suc))

  -- Ugly, but gets the job done.
  table-complete : n ≤ m → (f : Fin n → Fin m) → Injective f →
                   Σ (Table n m) (λ t → ⟦ t ⟧t ≐ f)
  table-complete {zero}           z≤n       f  finj = nil , (λ ())
  table-complete {suc n} {suc m}  (s≤s lt)  f  finj = (j ∷ t) , correct
    where
      j = f zero
      skipj = Permutations.skip j

      f≢j : ∀ i → j ≢ f (suc i)
      f≢j i eq = zero≢suc (finj eq)

      g : Fin n → Fin m
      g i = punchOut (f≢j i)

      g-correct : skipj ∘ g  ≐  f ∘ suc
      g-correct i = skip-punchOut (f≢j i)

      ginj : Injective g
      ginj {i} {i'} geq = suc-inj (finj (
          f (suc i)     ≡⟨ sym (g-correct i) ⟩
          skipj (g i)   ≡⟨ cong skipj geq ⟩
          skipj (g i')  ≡⟨ g-correct i' ⟩
          f (suc i')    ∎))

      rec = table-complete lt g ginj
      t = proj₁ rec
      tcorrect = proj₂ rec

      correct : ⟦ j ∷ t ⟧t ≐ f
      correct zero    = refl
      correct (suc i) = trans (cong skipj (tcorrect i)) (g-correct i)
\end{code}
