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

notation `Σ` := char

notation `Σ*` := list Σ

@[simp] def δ : state → Σ → list state
| q0 c0 := [q0]
| q1 c0 := [q2]
| q2 c0 := [q3]
| q3 c0 := []
| q0 c1 := [q0, q1]
| q1 c1 := [q2]
| q2 c1 := [q3]
| q3 c1 := []

@[simp] def δδ : state → Σ* → list state
| q [] := [q]
| q (c :: w') := (δ q c).bind (fun q', δδ q' w')

lemma δδ_correct_1 : ∀ (w : Σ*) (a b : Σ), q3 ∈ δδ q0 (w ++ [c1, a, b]) :=
  begin
    intros,
    induction w with c w', {
      rcases ⟨a, b⟩ with ⟨_ | _, _ | _⟩,
      all_goals { simp, },
    },
    cases c,
    all_goals { simp, tauto, },
  end

lemma q1_to_q3_2_inputs : ∀ w : Σ*, q3 ∈ δδ q1 w → ∃ a b, w = [a, b] :=
  begin
    intros w h,
    rcases w with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _ , w⟩⟩⟩,
    all_goals { simp at *, },
    all_goals { tauto, },
  end

lemma δδ_correct_2 : ∀ w : Σ*, q3 ∈ δδ q0 w → ∃ w' a b, w = w' ++ [c1, a, b] :=
  begin
    intros w h,
    induction w with c w ih1, {
      simp at h,
      tauto,
    },
    cases c, {
      simp at h,
      rcases ih1 h with ⟨w', a, b, rfl⟩,
      existsi [c0 :: w', a, b],
      simp,
    },
    simp at h,
    cases h, {
      rcases ih1 h with ⟨w', a, b, rfl⟩,
      existsi [c1 :: w', a, b],
      simp,
    },
    rcases q1_to_q3_2_inputs w h with ⟨a, b, rfl⟩,
    existsi [[], a, b],
    simp,
  end

theorem δδ_correct
: ∀ w : Σ*, q3 ∈ δδ q0 w ↔ ∃ (w' : Σ*) (a b : Σ), w = w' ++ [c1, a, b] :=
  begin
    intros,
    split, {
      apply δδ_correct_2,
    },
    intros h,
    rcases h with ⟨x, a, b, rfl⟩,
    apply δδ_correct_1,
  end

end AutomatonVerification