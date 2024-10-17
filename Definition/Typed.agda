{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --cubical-compatible #-}

module Definition.Typed where

open import Definition.Untyped hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product

infixl 30 _∙_
infix 30 Πⱼ_▹_
infix 30 Σⱼ_▹_
infix 30 ⟦_⟧ⱼ_▹_
infix 30 _∪ⱼ_


private
  variable
    n m : Nat
    Γ  : Con Term n
    A B F : Term n
    G : Term (1+ n)
    x : Fin n


-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term n) (Γ : Con Term n) → Set where
  here  :                       x0 ∷ wk1 A ∈ (Γ ∙ A)
  there : (h : x ∷ A ∈ Γ) → (x +1) ∷ wk1 A ∈ (Γ ∙ B)

mutual
  -- Well-formed context
  data ⊢_ : Con Term n → Set where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term n) : Term n → Set where
    Uⱼ     : ⊢ Γ → Γ ⊢ U
    ℕⱼ     : ⊢ Γ → Γ ⊢ ℕ
    Emptyⱼ : ⊢ Γ → Γ ⊢ Empty
    Unitⱼ  : ⊢ Γ → Γ ⊢ Unit
    Πⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Π F ▹ G
    Σⱼ_▹_  : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → Γ     ⊢ Σ F ▹ G
    _∪ⱼ_   : Γ ⊢ A
           → Γ ⊢ B
           → Γ ⊢ A ∪ B
    ∥_∥ⱼ   : Γ ⊢ A
           → Γ ⊢ ∥ A ∥
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ El A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set where
    Πⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Π′ F ▹ G ∷ U
    Σⱼ_▹_     : ∀ {F G}
              → Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → Γ     ⊢ Σ′ F ▹ G ∷ U
    _∪ⱼ_      : ∀ {A B}
              → Γ ⊢ A ∷ U
              → Γ ⊢ B ∷ U
              → Γ ⊢ A ∪′ B ∷ U
    ∥_∥ⱼ      : ∀ {A}
              → Γ ⊢ A ∷ U
              → Γ ⊢ ∥ A ∥′ ∷ U
    ℕⱼ        : ⊢ Γ → Γ ⊢ ℕ′ ∷ U
    Emptyⱼ    : ⊢ Γ → Γ ⊢ Empty′ ∷ U
    Unitⱼ     : ⊢ Γ → Γ ⊢ Unit′ ∷ U

    var       : ∀ {A x}
              → ⊢ Γ
              → x ∷ A ∈ Γ
              → Γ ⊢ var x ∷ A

    lamⱼ      : ∀ {F G t}
              → Γ     ⊢ F
              → Γ ∙ F ⊢ t ∷ G
              → Γ     ⊢ lam t ∷ Π F ▹ G
    _∘ⱼ_      : ∀ {g a F G}
              → Γ ⊢     g ∷ Π F ▹ G
              → Γ ⊢     a ∷ F
              → Γ ⊢ g ∘ a ∷ G [ a ]

    prodⱼ     : ∀ {F G t u}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]
              → Γ ⊢ prod t u ∷ Σ F ▹ G
    fstⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ F ▹ G
              → Γ ⊢ fst t ∷ F
    sndⱼ      : ∀ {F G t}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σ F ▹ G
              → Γ ⊢ snd t ∷ G [ fst t ]

    injlⱼ     : ∀ {A B t}
              → Γ ⊢ B
              → Γ ⊢ t ∷ A
              → Γ ⊢ injl t ∷ A ∪ B
    injrⱼ     : ∀ {A B t}
              → Γ ⊢ A
              → Γ ⊢ t ∷ B
              → Γ ⊢ injr t ∷ A ∪ B
    casesⱼ    : ∀ {A B C t u v}
              → Γ ⊢ t ∷ A ∪ B
              → Γ ⊢ u ∷ A ▹▹ C
              → Γ ⊢ v ∷ B ▹▹ C
              → Γ ⊢ C -- necessary?
              → Γ ⊢ cases C t u v ∷ C

    ∥ᵢⱼ       : ∀ {A t}
              → Γ ⊢ t ∷ A
              → Γ ⊢ ∥ᵢ t ∷ ∥ A ∥
    ∥ₑⱼ       : ∀ {A B a f}
              → Γ ⊢ a ∷ ∥ A ∥
              → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
              → Γ ⊢ B -- necessary?
              → Γ ⊢ ∥ₑ B a f ∷ ∥ B ∥

    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢       n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {G s z n}
              → Γ ∙ ℕ ⊢ G
              → Γ       ⊢ z ∷ G [ zero ]
              → Γ       ⊢ s ∷ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
              → Γ       ⊢ n ∷ ℕ
              → Γ       ⊢ natrec G z s n ∷ G [ n ]

    Emptyrecⱼ : ∀ {A e}
              → Γ ⊢ A → Γ ⊢ e ∷ Empty → Γ ⊢ Emptyrec A e ∷ A

    starⱼ     : ⊢ Γ → Γ ⊢ star ∷ Unit

    conv      : ∀ {t A B}
              → Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

  -- Type equality
  data _⊢_≡_ (Γ : Con Term n) : Term n → Term n → Set where
    univ   : ∀ {A B}
           → Γ ⊢ A ≡ B ∷ U
           → Γ ⊢ El A ≡ El B
    refl   : ∀ {A}
           → Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : ∀ {A B}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : ∀ {A B C}
           → Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    Π-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E
    Σ-cong : ∀ {F H G E}
           → Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E
    ∪-cong : ∀ {A B C D}
           → Γ ⊢ A ≡ B
           → Γ ⊢ C ≡ D
           → Γ ⊢ A ∪ C ≡ B ∪ D
    ∥-cong : ∀ {A B}
           → Γ ⊢ A ≡ B
           → Γ ⊢ ∥ A ∥ ≡ ∥ B ∥
    -- El congruence rules
    Elℕ-cong     : ⊢ Γ → Γ ⊢ El ℕ′ ≡ ℕ
    ElEmpty-cong : ⊢ Γ → Γ ⊢ El Empty′ ≡ Empty
    ElUnit-cong  : ⊢ Γ → Γ ⊢ El Unit′ ≡ Unit
    ElΠ-cong     : ∀ {F H G E}
                 → Γ     ⊢ F
                 → Γ     ⊢ F ≡ H ∷ U
                 → Γ ∙ F ⊢ G ≡ E ∷ U
                 → Γ     ⊢ El (Π′ F ▹ G) ≡ Π (El H) ▹ (El E)
    ElΣ-cong     : ∀ {F H G E}
                 → Γ     ⊢ F
                 → Γ     ⊢ F ≡ H ∷ U
                 → Γ ∙ F ⊢ G ≡ E ∷ U
                 → Γ     ⊢ El (Σ′ F ▹ G) ≡ Σ (El H) ▹ (El E)
    El∥-cong     : ∀ {A B}
                 → Γ ⊢ A ≡ B ∷ U
                 → Γ ⊢ El (∥ A ∥′) ≡ ∥ El B ∥
    El∪-cong     : ∀ {A B C D}
                 → Γ ⊢ A ≡ B ∷ U
                 → Γ ⊢ C ≡ D ∷ U
                 → Γ ⊢ El (A ∪′ C) ≡ (El B) ∪ (El D)
    El-cong      : ∀ {A B}
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ El A ≡ El B

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set where
    refl          : ∀ {t A}
                  → Γ ⊢ t ∷ A
                  → Γ ⊢ t ≡ t ∷ A
    sym           : ∀ {t u A}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ t ∷ A
    trans         : ∀ {t u r A}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ r ∷ A
                  → Γ ⊢ t ≡ r ∷ A
    conv          : ∀ {A B t u}
                  → Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ B
    Π-cong        : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F ⊢ G ≡ E       ∷ U
                  → Γ     ⊢ Π′ F ▹ G ≡ Π′ H ▹ E ∷ U
    Σ-cong        : ∀ {E F G H}
                  → Γ     ⊢ F
                  → Γ     ⊢ F ≡ H       ∷ U
                  → Γ ∙ F ⊢ G ≡ E       ∷ U
                  → Γ     ⊢ Σ′ F ▹ G ≡ Σ′ H ▹ E ∷ U
    ∪-cong        : ∀ {A B C D}
                  → Γ ⊢ A ≡ B ∷ U
                  → Γ ⊢ C ≡ D ∷ U
                  → Γ ⊢ A ∪′ C ≡ B ∪′ D ∷ U
    ∥-cong        : ∀ {A B}
                  → Γ ⊢ A ≡ B ∷ U
                  → Γ ⊢ ∥ A ∥′ ≡ ∥ B ∥′ ∷ U
    app-cong      : ∀ {a b f g F G}
                  → Γ ⊢ f ≡ g ∷ Π F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ]
    β-red         : ∀ {a t F G}
                  → Γ     ⊢ F
                  → Γ ∙ F ⊢ t ∷ G
                  → Γ     ⊢ a ∷ F
                  → Γ     ⊢ (lam t) ∘ a ≡ t [ a ] ∷ G [ a ]
    η-eq          : ∀ {f g F G}
                  → Γ     ⊢ F
                  → Γ     ⊢ f ∷ Π F ▹ G
                  → Γ     ⊢ g ∷ Π F ▹ G
                  → Γ ∙ F ⊢ wk1 f ∘ var x0 ≡ wk1 g ∘ var x0 ∷ G
                  → Γ     ⊢ f ≡ g ∷ Π F ▹ G
    fst-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ ⊢ fst t ≡ fst t' ∷ F
    snd-cong      : ∀ {t t' F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t' ∷ Σ F ▹ G
                  → Γ ⊢ snd t ≡ snd t' ∷ G [ fst t ]
    Σ-β₁          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ fst (prod t u) ≡ t ∷ F
    Σ-β₂          : ∀ {F G t u}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]
                  → Γ ⊢ snd (prod t u) ≡ u ∷ G [ fst (prod t u) ]
    Σ-η           : ∀ {p r F G}
                  → Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ p ∷ Σ F ▹ G
                  → Γ ⊢ r ∷ Σ F ▹ G
                  → Γ ⊢ fst p ≡ fst r ∷ F
                  → Γ ⊢ snd p ≡ snd r ∷ G [ fst p ]
                  → Γ ⊢ p ≡ r ∷ Σ F ▹ G
    -- disjoint union
    injl-cong     : ∀ {t t' A B}
                  → Γ ⊢ B
                  → Γ ⊢ t ≡ t' ∷ A
                  → Γ ⊢ injl t ≡ injl t' ∷ A ∪ B
    injr-cong     : ∀ {t t' A B}
                  → Γ ⊢ A
                  → Γ ⊢ t ≡ t' ∷ B
                  → Γ ⊢ injr t ≡ injr t' ∷ A ∪ B
    cases-cong    : ∀ {t t' u u' v v' A B C C'}
                  → Γ ⊢ A
                  → Γ ⊢ B
                  → Γ ⊢ C ≡ C'
                  → Γ ⊢ t ≡ t' ∷ A ∪ B
                  → Γ ⊢ u ≡ u' ∷ A ▹▹ C
                  → Γ ⊢ v ≡ v' ∷ B ▹▹ C
                  → Γ ⊢ cases C t u v ≡ cases C' t' u' v' ∷ C
    ∪-β₁          : ∀ {A B C t u v}
                  → Γ ⊢ B
                  → Γ ⊢ C -- necessary?
                  → Γ ⊢ t ∷ A
                  → Γ ⊢ u ∷ A ▹▹ C
                  → Γ ⊢ v ∷ B ▹▹ C
                  → Γ ⊢ cases C (injl t) u v ≡ u ∘ t ∷ C
    ∪-β₂          : ∀ {A B C t u v}
                  → Γ ⊢ A
                  → Γ ⊢ C -- necessary?
                  → Γ ⊢ t ∷ B
                  → Γ ⊢ u ∷ A ▹▹ C
                  → Γ ⊢ v ∷ B ▹▹ C
                  → Γ ⊢ cases C (injr t) u v ≡ v ∘ t ∷ C
    -- truncation
    ∥ᵢ-cong       : ∀ {t t' A}
                  → Γ ⊢ A
                  → Γ ⊢ t ≡ t' ∷ A
                  → Γ ⊢ ∥ᵢ t ≡ ∥ᵢ t' ∷ ∥ A ∥
    ∥ₑ-cong       : ∀ {a a′ f f′ A B B′}
                  → Γ ⊢ A
                  → Γ ⊢ B ≡ B′
                  → Γ ⊢ a ≡ a′ ∷ ∥ A ∥
                  → Γ ⊢ f ≡ f′ ∷ A ▹▹ ∥ B ∥
                  → Γ ⊢ ∥ₑ B a f ≡ ∥ₑ B′ a′ f′ ∷ ∥ B ∥
    ∥-β           : ∀ {A B a f}
                  → Γ ⊢ B
                  → Γ ⊢ a ∷ A
                  → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
                  → Γ ⊢ ∥ₑ B (∥ᵢ a) f ≡ f ∘ a ∷ ∥ B ∥
    -- numbers
    suc-cong      : ∀ {m n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
                  → Γ ∙ ℕ ⊢ F ≡ F′
                  → Γ     ⊢ z ≡ z′ ∷ F [ zero ]
                  → Γ     ⊢ s ≡ s′ ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ n ≡ n′ ∷ ℕ
                  → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero   : ∀ {z s F}
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ]
    natrec-suc    : ∀ {n z s F}
                  → Γ     ⊢ n ∷ ℕ
                  → Γ ∙ ℕ ⊢ F
                  → Γ     ⊢ z ∷ F [ zero ]
                  → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                  → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                          ∷ F [ suc n ]
    Emptyrec-cong : ∀ {A A' e e'}
                  → Γ ⊢ A ≡ A'
                  → Γ ⊢ e ≡ e' ∷ Empty
                  → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A
    η-unit        : ∀ {e e'}
                  → Γ ⊢ e ∷ Unit
                  → Γ ⊢ e' ∷ Unit
                  → Γ ⊢ e ≡ e' ∷ Unit

-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set where
  conv           : ∀ {A B t u}
                 → Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  app-subst      : ∀ {A B t u a}
                 → Γ ⊢ t ⇒ u ∷ Π A ▹ B
                 → Γ ⊢ a ∷ A
                 → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  β-red          : ∀ {A B a t}
                 → Γ     ⊢ A
                 → Γ ∙ A ⊢ t ∷ B
                 → Γ     ⊢ a ∷ A
                 → Γ     ⊢ (lam t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  fst-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ ⊢ fst t ⇒ fst t' ∷ F
  snd-subst      : ∀ {t t' F G}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ t' ∷ Σ F ▹ G
                 → Γ ⊢ snd t ⇒ snd t' ∷ G [ fst t ]
  Σ-β₁           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 → Γ ⊢ fst (prod t u) ⇒ t ∷ F
  Σ-β₂           : ∀ {F G t u}
                 → Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]
                 -- TODO(WN): Prove that 𝔍 ∷ G [ t ] is admissible
                 → Γ ⊢ snd (prod t u) ⇒ u ∷ G [ fst (prod t u) ]
  -- disjoint union
  cases-subst    : ∀ {t t' u v A B C}
                 → Γ ⊢ A
                 → Γ ⊢ B
                 → Γ ⊢ C -- necessary?
                 → Γ ⊢ u ∷ A ▹▹ C
                 → Γ ⊢ v ∷ B ▹▹ C
                 → Γ ⊢ t ⇒ t' ∷ A ∪ B
                 → Γ ⊢ cases C t u v ⇒ cases C t' u v ∷ C
  ∪-β₁           : ∀ {A B C t u v}
                 → Γ ⊢ B
                 → Γ ⊢ C -- necessary?
                 → Γ ⊢ t ∷ A
                 → Γ ⊢ u ∷ A ▹▹ C
                 → Γ ⊢ v ∷ B ▹▹ C
                 → Γ ⊢ cases C (injl t) u v ⇒ u ∘ t ∷ C
  ∪-β₂           : ∀ {A B C t u v}
                 → Γ ⊢ A
                 → Γ ⊢ C -- necessary?
                 → Γ ⊢ t ∷ B
                 → Γ ⊢ u ∷ A ▹▹ C
                 → Γ ⊢ v ∷ B ▹▹ C
                 → Γ ⊢ cases C (injr t) u v ⇒ v ∘ t ∷ C
  -- truncation
  ∥ₑ-subst       : ∀ {a a' f A B}
                 → Γ ⊢ A
                 → Γ ⊢ B
                 → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
                 → Γ ⊢ a ⇒ a' ∷ ∥ A ∥
                 → Γ ⊢ ∥ₑ B a f ⇒ ∥ₑ B a' f ∷ ∥ B ∥
  ∥-β            : ∀ {A B a f}
                 → Γ ⊢ B
                 → Γ ⊢ a ∷ A
                 → Γ ⊢ f ∷ A ▹▹ ∥ B ∥
                 → Γ ⊢ ∥ₑ B (∥ᵢ a) f ⇒ f ∘ a ∷ ∥ B ∥
  -- numbers
  natrec-subst   : ∀ {z s n n′ F}
                 → Γ ∙ ℕ ⊢ F
                 → Γ     ⊢ z ∷ F [ zero ]
                 → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ     ⊢ n ⇒ n′ ∷ ℕ
                 → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  natrec-zero    : ∀ {z s F}
                 → Γ ∙ ℕ ⊢ F
                 → Γ     ⊢ z ∷ F [ zero ]
                 → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc     : ∀ {n z s F}
                 → Γ     ⊢ n ∷ ℕ
                 → Γ ∙ ℕ ⊢ F
                 → Γ     ⊢ z ∷ F [ zero ]
                 → Γ     ⊢ s ∷ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
                 → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∷ F [ suc n ]
  Emptyrec-subst : ∀ {n n′ A}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A

-- Type reduction
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set where
  univ : ∀ {A B}
       → Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ El A ⇒ El B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set where
  id  : ∀ {A}
      → Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : ∀ {A A′ B}
      → Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term n) → Term n → Term n → Set
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_ : (Γ : Con Term n) → Term n → Term n → Set
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term n) (t u A : Term n) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term m) : (σ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ} → Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {A σ}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ subst (tail σ) A
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term m) : (σ σ′ : Subst m n) (Γ : Con Term n) → Set where
  id  : ∀ {σ σ′} → Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {A σ σ′}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢  head σ ≡ head σ′ ∷ subst (tail σ) A
      → Δ ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F
     → Γ ∙ F ⊢ G
     → Γ     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → Γ     ⊢ ⟦ W ⟧′ F ▹ G ∷ U
⟦ BΠ ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
⟦ BΣ ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G
