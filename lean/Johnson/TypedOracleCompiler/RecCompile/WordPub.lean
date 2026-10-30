-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/WordPub.lean: the bound of Johnson/TypedOracleCompiler/RecCompile/WordTwoStage.lean where the
coding is not fixed beforehand: it is the member of a family at public digests that are the hash
function's own answers.

Purpose: the front verifier's word under a root is read through a coding made of the digest of the
public files, and that digest is an answer of the function that is drawn. `pub_lift`
(Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean) says that such digests cost a bound nothing, under premises
on the makers, the verdict and the event. Here these are paid for the event `BadW`.

Main names. `Merkle.Events.HashEvent.filter_idle`: the hash event outlasts the striking of idle
events, those with no answer AND at which nothing occurs. `Rom.filter_strike`: what a test that
refuses one oracle's entries keeps of the one-block entries is not moved when the entries at a
string of that oracle are struck. `BadW W m y`: the hash event on both logs, or the word under the
first stage's root is another off the first log than off both. `EM_strike`, `badW_strike`: both
outlast the striking of the entries at a string of the spare oracle. `word_pr_pub`: the bound 2 (tC
+ tP + 1)² / 2^lam with the coding at the public algorithm's output.

How. `pub_lift` at the makers in two stages (`run2`, `wire2`, `strike2`); the class of makers is
"two query bounds", which wiring keeps; the verdict is `pure true`, which asks no string; the base
is `word_pr_two` at each fixed d.

Limits.
- Asked of the public algorithm: no coin; strings that code points of the spare oracle `OracleName.other`
  under every member of the family (`IsOther`); no string twice. The entries of `OracleName.other` are idle
  in `evM`: no answer, and nothing occurs. At the written family the premise is `isOther_mPub`
  (Johnson/Top/Pub/ArmFamily.lean).
- The public strings are fixed before the function is drawn.
- The event is on the two logs, the root and d alone. That a committer's run stands in a log, and
  what a decoder makes of the word, is used afterwards, at each function:
  Johnson/TypedOracleCompiler/RecCompile/OpensTwoStage.lean.
- Nothing on soundness (index binding included), opening-form binding, no two openings,
  correctness of extraction or whatever else names a committer or a prover.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.WordTwoStage
import Johnson.TypedOracleCompiler.RecCompile.PublicLift
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublicArm
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsKeyPublic

set_option autoImplicit false

noncomputable section

namespace Merkle.Events
variable {E D : Type} {Ev : Merkle.Events E D}

/-- The hash event outlasts the striking of idle events: those with no answer at which nothing
occurs. -/
theorem HashEvent.filter_idle (p : E → Bool)
    (hidle : ∀ e, p e = false → Ev.answer e = none ∧ Ev.occ e = []) {tr : List E}
    (h : Ev.HashEvent tr) : Ev.HashEvent (tr.filter p) := by
  obtain ⟨pre, e, post, c, rfl, hne, ha, e', he', ho⟩ := h
  have hpe : p e = true := by
    by_contra hh
    rw [(hidle e (Bool.eq_false_iff.2 hh)).1] at ha
    cases ha
  have hpe' : p e' = true := by
    by_contra hh
    have h0 : c ∈ Ev.occ e' := ho
    rw [(hidle e' (Bool.eq_false_iff.2 hh)).2] at h0
    cases h0
  refine ⟨pre.filter p, e, post.filter p, c, ?_, fun hh => hne (List.mem_filter.1 hh).1, ha,
    e', List.mem_filter.2 ⟨he', hpe'⟩, ho⟩
  rw [List.filter_append, List.filter_cons_of_pos hpe]

end Merkle.Events

namespace Rom
variable {Sp : OSpec} {lam : ℕ}

/-- What a test that refuses the entries of one oracle keeps of the one-block entries of a log of
strings is not moved when the entries at a string that codes a point of that oracle are struck. -/
theorem filter_strike (m : OracleCoding Sp lam) (s0 : List Bool) (P : QA Sp → Bool)
    (h0 : ∀ e : QA Sp, e.1 = (m.dec s0).1 → P e = false) :
    ∀ tr : Trace (rom lam),
      (singleTr m (TypedOracleCompiler.Compile.Batch.Cms.strike s0 tr)).filter P =
        (singleTr m tr).filter P
  | [] => rfl
  | e :: tr => by
    have ih := filter_strike m s0 P h0 tr
    obtain ⟨u, s, r⟩ := e
    cases u
    have e1 : singleTr m ((⟨(), s, r⟩ : QA (rom lam)) :: tr) =
        singleTr m [⟨(), s, r⟩] ++ singleTr m tr := singleTr_append m [⟨(), s, r⟩] tr
    by_cases hs : s = s0
    · subst hs
      have e2 : TypedOracleCompiler.Compile.Batch.Cms.strike s ((⟨(), s, r⟩ : QA (rom lam)) :: tr) =
          TypedOracleCompiler.Compile.Batch.Cms.strike s tr := by
        simp [TypedOracleCompiler.Compile.Batch.Cms.strike]
      have e3 : (singleTr m [(⟨(), s, r⟩ : QA (rom lam))]).filter P = [] := by
        refine List.filter_eq_nil_iff.2 fun x hx => ?_
        have hx1 : x.1 = (m.dec s).1 := by
          unfold singleTr at hx
          by_cases hb : m.blocks (m.dec s).1 = 1
          · simp [hb] at hx
            rw [hx]
          · simp [hb] at hx
        rw [h0 x hx1]
        exact Bool.false_ne_true
      rw [e2, ih, e1, List.filter_append, e3, List.nil_append]
    · have e2 : TypedOracleCompiler.Compile.Batch.Cms.strike s0 ((⟨(), s, r⟩ : QA (rom lam)) :: tr) =
          (⟨(), s, r⟩ : QA (rom lam)) :: TypedOracleCompiler.Compile.Batch.Cms.strike s0 tr := by
        simp [TypedOracleCompiler.Compile.Batch.Cms.strike, hs]
      have e4 : singleTr m ((⟨(), s, r⟩ : QA (rom lam)) ::
          TypedOracleCompiler.Compile.Batch.Cms.strike s0 tr) =
          singleTr m [⟨(), s, r⟩] ++ singleTr m (TypedOracleCompiler.Compile.Batch.Cms.strike s0 tr) :=
        singleTr_append m [⟨(), s, r⟩] _
      rw [e2, e4, e1, List.filter_append, List.filter_append, ih]

end Rom

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- The rare event of two stages, read through a coding: the hash event on both logs, or the word
under the first stage's root is another off the first log than off both. -/
def BadW (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {St β : Type} (y : ((Dig lam × St) × Trace (rom lam)) × (β × Trace (rom lam))) : Prop :=
  EM (singleTr m (y.1.2 ++ y.2.2)) ∨
    extEnc W (singleTr m y.1.2) y.1.1.1 ≠ extEnc W (singleTr m (y.1.2 ++ y.2.2)) y.1.1.1

/-- the test "no entry of the spare oracle" -/
def notOther (e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) : Bool :=
  match e.1 with
  | OracleName.other => false
  | _ => true

theorem EM_strike (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool)
    (h : IsOther m s) (tr : Trace (rom lam)) (hE : EM (singleTr m tr)) :
    EM (singleTr m (strike s tr)) := by
  have h1 : EM ((singleTr m tr).filter (notOther (W := W))) :=
    Merkle.Events.HashEvent.filter_idle _ (fun e he => by
      obtain ⟨o, q, r⟩ := e
      cases o <;> first | exact ⟨rfl, rfl⟩ | cases he) hE
  rw [← filter_strike m s (notOther (W := W)) (fun e he => by
    obtain ⟨o, q, r⟩ := e
    have : o = OracleName.other := he.trans h
    subst this
    rfl) tr] at h1
  exact Merkle.Events.HashEvent.of_filter _ h1

/-- The rare event outlasts the striking of the entries at a string of the spare oracle. -/
theorem badW_strike (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool)
    (h : IsOther m s) {St β : Type}
    (y : ((Dig lam × St) × Trace (rom lam)) × (β × Trace (rom lam))) (hy : BadW W m y) :
    BadW W m (strike2 s y) := by
  unfold BadW strike2 at *
  rcases hy with hy | hy
  · left
    show EM (singleTr m (strike s y.1.2 ++ strike s y.2.2))
    rw [strike_append]
    exact EM_strike m s h _ hy
  · right
    show extEnc W (singleTr m (strike s y.1.2)) y.1.1.1 ≠
      extEnc W (singleTr m (strike s y.1.2 ++ strike s y.2.2)) y.1.1.1
    rw [strike_append, extEnc_strike m s (isOther_tree m s h),
      extEnc_strike m s (isOther_tree m s h)]
    exact hy

/-- **The price with the coding hanging on public digests that are the hash function's own
answers.** Two makers over one hash function, the first of which publishes a root; behind them a
public algorithm Pub, without coins, which asks strings of the spare oracle alone, none twice; the
coding is the family's member at its output. The rare event has probability at most
2 (tC + tP + 1)² / 2^lam. -/
theorem word_pr_pub {D : Type} (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hPt : ∀ d s, Pt s → IsOther (m d) s) (Pub : OComp (rom lam) D) (hnc : Pub.NoCoin)
    (hasks : Pub.AsksIn fun _ s => Pt s) (hnr : NoRepeat Pub) {St β : Type}
    (Ct : OComp (rom lam) (Dig lam × St)) (P2 : St → OComp (rom lam) β) (tC tP : ℕ)
    (hC : Ct.QueryBound tC) (hP : ∀ st, (P2 st).QueryBound tP) :
    Rom.Pr (expP (fun _ _ => OComp.pure true) Pub (run2 Prod.snd (Ct, P2)))
        (fun _ => {x | x.2.2 = true ∧ BadW W (m x.2.1) x.1}) ≤
      2 * ((tC + tP + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine pub_lift (run2 Prod.snd) wire2 strike2 (run2_wire Prod.snd)
    (fun M => M.1.QueryBound tC ∧ ∀ st, (M.2 st).QueryBound tP)
    (fun s r M hM => ⟨queryBound_wire s r _ _ hM.1, fun st => queryBound_wire s r _ _ (hM.2 st)⟩)
    (fun _ _ => OComp.pure true) (fun _ _ _ => rfl) Pt (fun _ _ => trivial)
    (fun d y => BadW W (m d) y) (fun d s y hs hy => badW_strike (m d) s (hPt d s hs) y hy) _ ?_
    Pub hnc hasks hnr (Ct, P2) ⟨hC, hP⟩
  intro d M hM
  refine le_trans ?_ (word_pr_two (W := W) hlam (m d) M.1 M.2 tC tP hM.1 hM.2)
  refine MeasureTheory.lintegral_mono fun g => ?_
  unfold PrCoins expD run2
  simp only [OComp.bind_assoc, OComp.runEager_bind, OComp.bind, OComp.runEager]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  exact pr_pure_le_pure fun h => h.2

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms Merkle.Events.HashEvent.filter_idle
#print axioms Rom.filter_strike
#print axioms TypedOracleCompiler.Compile.Batch.Cms.EM_strike
#print axioms TypedOracleCompiler.Compile.Batch.Cms.badW_strike
#print axioms TypedOracleCompiler.Compile.Batch.Cms.word_pr_pub
