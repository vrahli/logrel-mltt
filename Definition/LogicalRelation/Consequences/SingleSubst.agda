module Definition.LogicalRelation.Consequences.SingleSubst where

open import Definition.Untyped

open import Definition.Typed

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Soundness
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Fundamental
open import Definition.LogicalRelation.Consequences.Injectivity

open import Data.Product


substType : ∀ {t F G Γ} → Γ ∙ F ⊢ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substType ⊢G ⊢t with fundamental ⊢G | fundamentalTerm ⊢t
substType {t} {F} {G} ⊢G ⊢t | [Γ] , [G] | [Γ]' , [F] , [t] =
  let [G]' = S.irrelevance {A = G} [Γ] ([Γ]' ∙ [F]) [G]
      [G[t]] = substS {F} {G} {t} [Γ]' [F] [G]' [t]
  in  soundnessₛ [Γ]' [G[t]]

substTypeΠ : ∀ {t F G Γ} → Γ ⊢ Π F ▹ G → Γ ⊢ t ∷ F → Γ ⊢ G [ t ]
substTypeΠ ΠFG t with Π-inj ΠFG
substTypeΠ ΠFG t | F , G = substType G t
