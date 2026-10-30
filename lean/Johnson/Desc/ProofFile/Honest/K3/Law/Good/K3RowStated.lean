-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Good/K3RowStated.lean: THE PREMISES `RowStated`
(Honest/K3/Law/Good/K3ExactStated.lean) HOLD AT THE LOOKUP'S OWN SIDE. Public facts on declared
rounds alone. Theorems; no definition.

  `zip_bare` entries declared bare, beside an empty list of oracle messages each, as one list of
    pairs
  `rounds_k3` a member's rounds are a stretch es' of the member's entries, declared bare, without an
    oracle message; and es' are, but for the work bits, its stage's own entries
  `rowStated_of` `RowStated` at the side. CONDITIONAL ON the five premises of `fits_k3`
    (Honest/K3/Law/Good/K3Lettered.lean)
  `rowStated_k3` the same at a description's first chain, from `k3Fits`: under the binders of
    `fits_k3_of_fits`

They call: `member_k3` (Honest/K3/Law/Good/K3Members.lean); `entries_at` (Honest/K3/RowAt.lean);
`shapeOk_shape` (Honest/K3/Law/StageFacts.lean); `statedBy_like`, `statedBy_nums`
(Honest/SumLaw/Fits.lean) and `betaMarked_of_like` (Honest/SumLaw/BetaMarked.lean), which read no
work bit.

Limits. It shows the premise `RowStated` of the first of the two sentences of
Honest/K3/Law/Good/K3ExactStated.lean; of the sentences it shows nothing. The premise on the book
(`OwnsNone`) is not spoken of. No instance of these hypotheses is exhibited in this file. Elsewhere:
Honest/K3/Law/Good/K3RowStatedGuards.lean [not in this library] (a test)
has ten such sides at a small made-up public part, by evaluation; and under the
head `P5J.AtMgA` a side is seated at every site, over whatever row: `seated_head`
(Honest/K3/Law/Thread/ExactKeptHead.lean).
Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3ExactStated
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Members
import Johnson.Desc.ProofFile.Honest.K3.Law.StageFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription Oracle)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open ProofFile.Honest.SumLaw (StatedBy betaMarked statedBy_like statedBy_nums betaMarked_of_like)
open ProofFile.Honest.Small (statedOf)

local notation "FS" => VerifiableInference.Desc.First.S

/-- Entries declared bare, beside an empty list of oracle messages each. No premise. -/
theorem zip_bare : ∀ es : List Fmt.Entry,
    (es.map declOf).zip (es.map fun _ => ([] : List Oracle)) = es.map fun e => (declOf e, [])
  | [] => rfl
  | e :: es => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.zip_cons_cons, zip_bare es]

section
variable {S Cl V W X Pb : Type}

/-- **A member's rounds are its stage's own entries, but for the work bits, declared bare.**
CONDITIONAL ON the side, the four facts on the member found and the face, and the member's stage. -/
theorem rounds_k3 (A : Fill W) (s : Site) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl V W X Pb) (h : Side.seated bs s.at_.place (rowPairs A s) fs = some σ)
    (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit s.at_.face es = true)
    (hok : s.at_.face.ok = true) (u : Member V W X Pb) (hu : u ∈ σ.members) (st : Stage)
    (hst : (stages s.at_.face)[u.number]? = some st) :
    ∃ es' : List Fmt.Entry, u.rounds = es'.map (fun e => (declOf e, [])) ∧
      (es'.map fun e => { e with work := 0 }) = Stage.entries s.at_.face st := by
  obtain ⟨st', hst', hrs, _, _⟩ := member_k3 A s bs fs σ h u hu
  obtain rfl : st' = st := Option.some.inj (hst'.symm.trans hst)
  have h2 : 2 ≤ s.at_.face.planes := by
    unfold VerifiableInference.Desc.K3.Face.ok at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1.1.1.1.2
  have he : (es.map fun e => { e with work := 0 }) = entriesV s.at_.face := by
    unfold entriesFit at hfit
    exact of_decide_eq_true (by simpa using hfit)
  refine ⟨(es.drop (firstRound s.at_.face st')).take (Stage.rounds s.at_.face st'), ?_, ?_⟩
  · rw [hrs, hr, ho, zip_bare, List.map_take, List.map_drop]
  · rw [List.map_take, List.map_drop, he]
    exact entries_at s.at_.face h2 st' (List.mem_of_getElem? hst)

/-- **The premises hold at the side.** Conditional on the side and on: the member found declares
just the entries es, bare; it states an empty list of oracle messages for each; es are, but for the
work bits, the entries that the hearing goes by; the face passes its own test. No instance of these
hypotheses is exhibited in this file. -/
theorem rowStated_of (A : Fill W) (s : Site) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl V W X Pb) (h : Side.seated bs s.at_.place (rowPairs A s) fs = some σ)
    (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit s.at_.face es = true)
    (hok : s.at_.face.ok = true) : RowStated s.at_.face σ := by
  constructor
  · intro u hu st k hst hk
    obtain ⟨es', e1, e2⟩ := rounds_k3 A s bs fs σ h es hr ho hfit hok u hu st hst
    have e3 : (es'.map fun e => { e with work := 0 }) =
        VerifiableInference.Desc.Part.MaskedSum.entries k := by
      rw [e2]
      unfold Stage.entries
      rw [hk]
    refine ⟨shapeOk_shape hok st k hk, statedBy_like k u.rounds ?_ ?_,
      betaMarked_of_like k u.rounds ?_⟩
    · rw [e1, ← e3, List.map_map, List.map_map]
      rfl
    · intro r hr'
      rw [e1] at hr'
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr'
      rfl
    · rw [e1, ← e3, List.map_map, List.map_map]
      rfl
  · intro u hu st hst hk
    obtain ⟨es', e1, e2⟩ := rounds_k3 A s bs fs σ h es hr ho hfit hok u hu st hst
    have e3 : (es'.map fun e => { e with work := 0 }) =
        [VerifiableInference.Desc.K3.drawEntry st.name (st.draws s.at_.face)] := by
      rw [e2]
      unfold Stage.entries
      rw [hk]
    have hS : StatedBy [0] u.rounds := by
      refine statedBy_nums [0] u.rounds ?_ ?_
      · have e4 : u.rounds.map (fun r => (r.1.entry.msg, r.1.entry.answers, r.1.entry.roots)) =
            (es'.map fun e => { e with work := 0 }).map fun e => (e.msg, e.answers, e.roots) := by
          rw [e1, List.map_map, List.map_map]
          rfl
        rw [e4, e3]
        rfl
      · intro r hr'
        rw [e1] at hr'
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr'
        rfl
    match hu' : u.rounds, hS with
    | [r], hS =>
      obtain ⟨a1, a2, _⟩ := hS
      show [(r.1.items.filter (· != .root), r.2)] = [([], [])]
      rw [a1, a2]
      rfl

end

section
variable {V W X Pb : Type}

/-- **The same at a description's first chain, from "fits".** Conditional on the description's
return, the site, the lot's sub-protocol at the site's place, `k3Fits` at the chain's flat list, and
the side. No instance of these hypotheses is exhibited in this file. -/
theorem rowStated_k3 (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A₀ : SharedSeat)
    (B₀ : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A₀ B₀) (s : Site)
    (hs : s ∈ lookSites Z) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : b.place = s.at_.place) (hF : k3Fits Z ch.blocksInOrder s = true) (A : Fill W)
    (fs : List (Fall FS)) (σ : Side FS ProofFile.Cl V W X Pb)
    (h : Side.seated ch.blocksInOrder s.at_.place (rowPairs A s) fs = some σ) :
    RowStated s.at_.face σ := by
  have hf : ch.blocksInOrder.find? (fun b => b.place == s.at_.place) = some σ.block := by
    unfold Side.seated at h
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hm
  have hp : σ.block.place = s.at_.place := by simpa using List.find?_some hf
  obtain ⟨m', hf', hk⟩ := plan_of_fits Z ch.blocksInOrder s hF
  obtain rfl : m' = σ.block := Option.some.inj (hf'.symm.trans hf)
  have hm : σ.block ∈ ch.blocksInOrder := List.mem_of_find?_eq_some hf
  have hmp : σ.block.place = b.place := hp.trans hbs.symm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block o pol lay KL Fd Z Bs base ch A₀ B₀ O s hs b σ.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A₀ B₀ O b hb σ.block hm hmp
  exact rowStated_of A s ch.blocksInOrder fs σ h (s.p.entries.getD []) (g1.trans e3) (g2.trans e4) e1
    (fits_gives Z ch.blocksInOrder s hF).2.2.1

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.zip_bare
#print axioms ProofFile.Honest.K3.Law.rounds_k3
#print axioms ProofFile.Honest.K3.Law.rowStated_of
#print axioms ProofFile.Honest.K3.Law.rowStated_k3
