import Mathlib.Data.Fintype.CardEmbedding

open Set

noncomputable section
namespace PALRH.LocalAgreement

/-- A record's assigned physical slot agrees in every chart that actually includes it. -/
def consistent {A B I : Type*} (live : I → A → Prop) (slot : I → A → B) (a : A) :=
  ∀ i j, live i a → live j a → slot i a=slot j a

/-- If each pair of records can be seen together, consistent records have a joint injection. -/
theorem consistent_count {A B I : Type*} [Fintype A] [Fintype B]
    (live : I → A → Prop) (slot : I → A → B) [DecidablePred (consistent live slot)]
    (see : ∀ a b : A, ∃ i : I, live i a ∧ live i b)
    (inside : ∀ i, InjOn (slot i) {a | live i a}) :
    Fintype.card {a : A // consistent live slot a}≤Fintype.card B := by
  classical
  let atRecord (a : A) := Classical.choose (see a a)
  have kept (a : A) : live (atRecord a) a := (Classical.choose_spec (see a a)).1
  let joint : {a : A // consistent live slot a} → B := fun a => slot (atRecord a.val) a.val
  apply Fintype.card_le_of_injective joint
  intro a b eq
  obtain ⟨i,ha,hb⟩:=see a.val b.val
  apply Subtype.ext
  apply inside i ha hb
  calc
    slot i a.val = joint a := a.property _ _ ha (kept _)
    _ = joint b := eq
    _ = slot i b.val := b.property _ _ (kept _) hb

/-- The stronger hypothesis that every record is consistent glues all local maps on their overlaps. -/
theorem complete_count {A B I : Type*} [Fintype A] [Fintype B]
    (live : I → A → Prop) (slot : I → A → B)
    (see : ∀ a b : A, ∃ i : I, live i a ∧ live i b)
    (inside : ∀ i, InjOn (slot i) {a | live i a}) (agree : ∀ a, consistent live slot a) :
    Fintype.card A≤Fintype.card B := by
  classical
  have h:=consistent_count live slot see inside
  let full : A → {a : A // consistent live slot a} := fun a => ⟨a,agree a⟩
  exact (Fintype.card_le_of_injective full (fun _ _ e => congrArg Subtype.val e)).trans h

#print axioms PALRH.LocalAgreement.consistent_count
#print axioms PALRH.LocalAgreement.complete_count
end PALRH.LocalAgreement
