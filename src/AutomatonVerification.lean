import tactic

namespace AutomatonVerification

inductive state : Type
| q0
| q1
| q2
| q3

open state

inductive char : Type
| c0
| c1

open char

notation `string` := list char

@[simp] def δ : state → char → list state
| q0 c0 := [q0]
| q1 c0 := [q2]
| q2 c0 := [q3]
| q3 c0 := []
| q0 c1 := [q0, q1]
| q1 c1 := [q2]
| q2 c1 := [q3]
| q3 c1 := []

@[simp] def δδ : state → string → list state
| q [] := [q]
| q (c :: w') := (δ q c).bind (fun q', δδ q' w')

lemma δδ_correct_1 : ∀ (w : string) (a b : char), q3 ∈ δδ q0 (w ++ [c1, a, b]) :=
  begin
    intros,
    induction w with c w', {
      cases a,
      all_goals { cases b, },
      all_goals { simp, },
    },
    cases c,
    all_goals { simp, tauto, },
  end

lemma q1_to_q3_2_inputs : ∀ w : string, q3 ∈ δδ q1 w → ∃ a b, w = [a, b] :=
  begin
    intros w h,
    cases w with c w, {
      simp at *,
      tauto,
    },
    cases c,
    all_goals {
      simp at *,
      cases w with a w, {
        simp at *,
        tauto,
      },
      cases a,
      all_goals {
        simp at *,
        cases w with a w,
        refl,
        cases a,
        all_goals { simp at *, tauto, },
      },
    },
  end

lemma δδ_correct_2 : ∀ w : string, q3 ∈ δδ q0 w → ∃ w' a b, w = w' ++ [c1, a, b] :=
  begin
    intros w h,
    induction w with c w ih1, {
      simp at h,
      tauto,
    },
    cases c, {
      simp at h,
      rcases ih1 h with ⟨w', ⟨a, ⟨b, ih2⟩⟩⟩,
      subst w,
      existsi [c0 :: w', a, b],
      simp, 
    },
    simp at h,
    cases h, {
      rcases ih1 h with ⟨w', ⟨a, ⟨b, ih2⟩⟩⟩,
      subst w,
      existsi [c1 :: w', a, b],
      simp, 
    },
    rcases q1_to_q3_2_inputs w h with ⟨a, ⟨b, h2⟩⟩,
    subst w,
    existsi [[], a, b],
    simp,
  end

theorem δδ_correct : ∀ w : string, q3 ∈ δδ q0 w ↔ ∃ x a b, w = x ++ [c1, a, b] :=
  begin
    intros,
    split, {
      apply δδ_correct_2,
    }, {
      intros h,
      rcases h with ⟨x, ⟨a, ⟨b, h⟩⟩⟩,
      subst w,
      apply δδ_correct_1,
    },
  end

end AutomatonVerification