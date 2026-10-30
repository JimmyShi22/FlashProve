-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CountFrom.lean: THE SMALLNESS TEST: THE FORM OF A COUNT FOR A TEST BEHIND THE
BATCHING, THE TEST A LETTER; AND THAT COUNT AT A SEGMENT WHOSE RUNS OF CLAIMS ARE PLAIN.
Definitions, statements and proofs. No prover. Lemmas; none of the library's goals. An assembly: no
new argument.

  `PlainLink L`   what `gathers_of_plain` (Johnson/Desc/K8/Honest/GathersPlain.lean) and
      `funs_of_yes` (FallAtt.lean) ask of a segment L: its order is a list pre, the run
      "K8.equations", a list post; the runs of pre and of post are plain (`PreOk`, `PostOk`); the
      run "K8.equations" is the library's
  `plain_layers`, `plain_att`, `plain_head`   so is a segment of each of the three kinds, under that
      kind's ties
  `CountFrom ok no N`   the form of `FallFew` (FallCount.lean), the test a letter: ok: a test with
      code on the data and the ledger in front; no: a test on the state behind; N: a number of the
      data. IF batch's yeses at s are the batching block's, s holds tl and F, ok tl F says yes, g
      meets `Gathers` at s, and d bounds the exponents: THEN at most N tl * d field elements are
      challenges at which batch says yes and, behind it, no says yes
  `planes_from`, `digits_from`, `units_from`   `planes_few` (PlanesFew.lean), `digits_few`
      (DigitsFew.lean) and `fall_few` (FallFew.lean) in that form
  **`count_at_link`**   a count of that form, at a plain segment: (hok) whatever data and ledger s
      holds pass ok, with N tl ≤ n; (hd) d bounds the exponents at whatever s holds: at most n * d
Limits. (hok) and (hd) are premises. Nothing on which states meet them.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallHead
import Johnson.Desc.K8.Honest.PlanesFew
import Johnson.Desc.K8.Honest.DigitsFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.Kinds.Head
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-- What the general lemmas ask of a segment. -/
def PlainLink (L : Link S Claim) : Prop :=
  ∃ (i : Nat) (pre post : List (Nat × String)),
    L.order = pre ++ (i, "K8.equations") :: post ∧ PreOk L pre ∧ PostOk L post ∧
    ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2

theorem plain_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) : PlainLink L := by
  refine ⟨4, [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")],
    [(2, "back")], by rw [hord]; rfl, ?_, ?_, ties.tEq⟩
  · intro o ho run hat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, plain_objectsCalls⟩
    · exact ⟨_, ties.tGuests 1 (by simp) run hat, plain_idle⟩
    · obtain ⟨r, l, u⟩ := ties.tFront run hat
      exact ⟨r, u, plain_front p4 r l⟩
    · exact ⟨_, tD run hat, plain_objectsDigits⟩
    · exact ⟨_, ties.tGuests 6 (by simp) run hat, plain_idle⟩
  · intro o ho run hat
    obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
    obtain ⟨r, l, u⟩ := ties.tBack run hat
    exact ⟨r, u, behind_back p4 r l⟩

theorem plain_att (L : Link S Claim) (c : P.ParC) (nU : Array Nat)
    (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (K9.joinCalls (P.keysOfK (P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (P.readersOfK (P.seatCO c) c)))
    (hord : L.order = orderOf .attention) : PlainLink L :=
  ⟨4, attPre, [], by rw [hord]; rfl, att_pre L c nU ties tC tD tJ tP, post_nil L, ties.tEq⟩

theorem plain_head (L : Link S Claim) (hS : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L hS iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt iU3))))
    (hord : L.order = orderOf .head) : PlainLink L :=
  ⟨5, headPre, headPost, by rw [hord]; rfl, head_pre L hS iU3 l piece p6 nU ties tC tD tP,
    head_post L hS iU3 l piece p6 nU ties, ties.tEq⟩

/-- **The form of a count, the test a letter.** -/
def CountFrom (ok : HTailF2 → Fork → Bool) (no : S → Bool) (N : HTailF2 → ℕ) : Prop :=
  ∀ (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
    (∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t) →
    tlForkP.get? s = some (tl, F) → ok tl F = true → Gathers p g s tl funs nf nb a →
    F.planClaimsF + topOf tl funs ≤ d + 1 →
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ N tl * d

theorem planes_from :
    CountFrom (fun tl _ => planesLaid tl && planesLive tl) planesNo
      (fun tl => 3 * tl.bzColumns) := by
  intro p g batch s tl F funs nf nb d a hb hs hok hG hd
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
  exact planes_few p g batch s tl F funs nf nb d a hb hs h1 h2 hG (by omega)

theorem digits_from :
    CountFrom (fun tl F => digitsLaid tl F && digitsLive tl) digitsNo
      (fun tl => 2 * (tl.zzBlocks * tl.mz)) := by
  intro p g batch s tl F funs nf nb d a hb hs hok hG hd
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
  exact digits_few p g batch s tl F funs nf nb d a hb hs h1 h2 hG (by omega)

/-- `fall_few` in that form: the count for `selfUnits`. -/
theorem units_from (nU : Array Nat) (tU : Nat) :
    CountFrom (fun tl _ => unitsLaid nU tl tU) (zeroUnitAt nU) (fun _ => nU.getD 2 0) := by
  intro p g batch s tl F funs nf nb d a hb hs hok hG hd
  exact fall_few p g batch nU s tl F funs tU nf nb d a hb hs hok hG hd

/-- **The count at a plain segment.** -/
theorem count_at_link {ok : HTailF2 → Fork → Bool} {no : S → Bool} {N : HTailF2 → ℕ}
    (C : CountFrom ok no N) (L : Link S Claim) (hL : PlainLink L) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (n d : Nat)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hok : ∀ tl F, s.tl? = some tl → s.fork? = some F → ok tl F = true ∧ N tl ≤ n)
    (hd : ∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ n * d := by
  obtain ⟨i, pre, post, hord, Hpre, Hpost, tEq⟩ := hL
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch no s [chiAt x] = true
  · obtain ⟨x, hx⟩ := hne
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      obtain ⟨t, e, cls, y, G, hdr, hg, -, -, -⟩ := batch_ok p _ s t' (chiAt x) (hb _ _ hbt)
      obtain ⟨a0, -, -, ha0, -, -, -⟩ := drawnAt_ok p s t (chiAt x) hdr
      have hF : s.fork? = some a0.F := K9.get_fork s a0 ha0
      obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1
        (funs_of_yes L p i pre post hord Hpre Hpost tEq s _ t e cls hdr hg)
      obtain ⟨tl, ht⟩ : ∃ tl, s.tl? = some tl := by
        cases h : s.tl? with
        | some tl => exact ⟨tl, rfl⟩
        | none =>
          exfalso
          simp [K9.atS, h] at ha0
      obtain ⟨nf, nb, a, hGa⟩ := gathers_of_plain L p i pre post hord Hpre Hpost tEq s tl funs ht hf
      obtain ⟨h1, h2⟩ := hok tl a0.F ht hF
      exact (C p _ batch s tl a0.F funs nf nb d a hb ((tlFork_iff s tl a0.F).2 ⟨ht, hF⟩) h1 hGa
        (hd _ _ _ ht hF hf)).trans (Nat.mul_le_mul_right d h2)
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.plain_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_att
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_head
#print axioms VerifiableInference.Desc.First.K8.Honest.planes_from
#print axioms VerifiableInference.Desc.First.K8.Honest.digits_from
#print axioms VerifiableInference.Desc.First.K8.Honest.units_from
#print axioms VerifiableInference.Desc.First.K8.Honest.count_at_link
