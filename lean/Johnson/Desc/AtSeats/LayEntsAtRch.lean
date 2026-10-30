-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/LayEntsAtRch.lean: **jLay2_at_reads**: THE CLAUSE `JLay2` (Johnson/Desc/K1/Law/ArmLayIn.lean: what stays of
the feed-forward links' half of the exchange that is these links' own) ALONG THE STATES THAT THE VERIFIER REACHES,
IN FRONT OF EACH LINK's READS, in hJ's own letters (armOk_at_rch's, Johnson/Desc/AtSeats/ArmAtRch.lean).
HOW. The state stands behind K4's accept at the link's own parameters (`kept_at_reads`,
Johnson/Desc/AtSeats/KeptAtRch.lean). Its first clause: `u3_of_kept`. Its second, run by run (`layRuns` [kernel]: the row's
runs are four): (2, "front") | (2, "back"): the reader's answer is the run's own list (`forms_of_reader`), and
`ents_front` | `ents_back` (Johnson/Road/K4/ArmKept.lean) say of each entry of such a list what
the clause asks · (1, "objects") | (1, "guests"): where the rows that the lookup heard are bare no form names an entry
(`reader_bare`, `k3At_else_bare`, Johnson/Desc/K1/Law/ArmElsePaid.lean).
  `LayLines W g hp`  ON LETTERS: five lines on the public parameters, which `ents_front` | `ents_back` ask: hK hm hg htm hNM
  `PadAt s`          THE LOOKUPS' CLAUSE, ON THE STATE IN FRONT ALONE: what the lookup on the calls left names no entry
                   (`Fo.Tp.PadNames` at some ledger; `RowsBare`)
  `reader_of_forms`  at a link that is not the output head's the link's reader is the run itself
  `states1_bare`     block 1 of a link l < 24
  `jLay2_of_kept`    JLay2 from KeptAt, PadAt and the lines
  `jLay2_at_reads`   **the clause along "reached"**
PREMISES LEFT: hS hR O · hWX hDlk hlk hX24 (on letters) · hLines · hPad : PadAt along "reached" in front of the feed-forward
links' reads (THE LOOKUPS' LAW BEHIND THEIR ACCEPT, AND "K4 leaves what the lookup heard": `Rest`: NOT CALLED HERE).
What is not claimed. The premises. Nothing on soundness.
The recursion limit is raised in this file (maxRecDepth 1000000): for the kernel's evaluations' elaboration alone.

-/
import Johnson.Desc.AtSeats.KeptAtRch
import Johnson.Desc.K1.Law.ArmElsePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block Chain FileDescription Link Claim)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MgData rowQ linkNo runsAt onQ Frame)
open VerifiableInference.Desc.K9 (readerOf statesOfLink readersOfLink holesAt RunOf)
open VerifiableInference.OnPublicFiles (headLink)
open Johnson.Desc.First.Walk.Tied (RchAt)
open IM (k1Ix)
open ProofFile (Cl)

/-- The row's runs at a feed-forward link. -/
def layRunsB (n : ℕ) : Bool :=
  (List.range n).all fun l =>
    !((linksFull[l]?).getD .layers == .layers) ||
      (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins.all fun it =>
        match it with
        | .formsT m j nm => (runsAt linksFull m j nm).all fun p =>
            p == (2, "front") || p == (2, "back") || p == (1, "objects") || p == (1, "guests")
        | _ => true

theorem layRuns : layRunsB 25 = true := by decide +kernel

/-- The test can fail: an attention link's runs are others. -/
theorem layRuns_fails :
    ((runsAt linksFull 1 3 "own").all fun p =>
      p == (2, "front") || p == (2, "back") || p == (1, "objects") || p == (1, "guests")) = false := by
  decide +kernel

/-- **Five lines on the public parameters.** -/
structure LayLines (W : Verify.Public) (g : ℕ) (hp : Layer.HPlan2) : Prop where
  hK : hp.nU.getD 2 0 ≤ ((hp.Fp.trees[u3Of hp.tl]?).map (·.K)).getD 0
  hm : ((W.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = OnBytes.Road.matsR W.layers.y g
  hg : g < W.layers.y.NGr
  htm : (hp.tl.mats.map fun M => (M.m, M.k)) = OnBytes.Road.matsR W.layers.y g
  hNM : hp.tl.NM = hp.tl.mats.size

/-- **What the lookup on the calls left names no entry.** -/
def PadAt (s : S) : Prop :=
  (∀ b₀ fo, s.here = .lay b₀ → b₀.fo = some fo → ∃ F', Fo.Tp.PadNames fo F') ∧ RowsBare s

/-- At a link that is not the output head's the link's reader is the run itself. -/
theorem reader_of_forms {XV : Verify.Public} {l : ℕ} (hne : (l == headLink XV) = false)
    (lk : Link S Claim) {b : ℕ} {name : String} (hn : (name == "K8.equations") = false) {s : S}
    {R : K9.Read}
    (h : (readersOfLink (holesAt XV (headLink XV) l lk) lk).forms b name s = some R) :
    readerOf (statesOfLink lk) b name s = some R := by
  have h' : (if (name == "K8.equations") = true then (holesAt XV (headLink XV) l lk).small s
    else match readerOf (statesOfLink lk) b name s with
      | some R => some R
      | Option.none => (holesAt XV (headLink XV) l lk).silent b name s) = some R := h
  rw [if_neg (by rw [hn]; exact Bool.false_ne_true)] at h'
  cases hr : readerOf (statesOfLink lk) b name s with
  | some R' =>
    rw [hr] at h'
    exact h'
  | none =>
    exfalso
    rw [hr] at h'
    simp [holesAt, hne] at h'

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Block 1 of a link l < 24. -/
theorem states1_bare (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 24)
    (lk : Link S Cl) (eL : c.links[l]? = some lk) (name : String) (hn : name ≠ "planes") :
    ∀ r, (statesOfLink lk 1).find? (fun r => r.1 == name) = some r → BareRun r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O l (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have hix : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  rw [hix] at e2
  intro r hr
  have hb := List.find?_some (p := fun r : RunOf S => r.1 == name) hr
  have hnm : r.1 = name := eq_of_beq hb
  have hm : r ∈ statesOfLink lk 1 := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [e2] at hm
  have hm' : r ∈ b.claims := hm
  rw [IM.claims_alone la] at hm'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm'
  refine bare_guard _ _ (k3At_else_bare Bs.G₀.W Z _ ?_ b' k3 q hq (by
    intro e
    exact hn (hnm.symm.trans e)))
  show (IM.k3Place l false).piece ≤ 3
  unfold IM.k3Place
  rw [hix]
  show (1 + 1 : ℕ) ≤ 3
  omega

/-! ## The clause -/

section
open OnBytes.Desc.First.K4 (blockAtC block seatOwn frontOf formsBack formsFrontWith hearFl block_front
  block_back)
open OnBytes.Desc.First.K4.Total (frontOf_eq run_pub)
open OnBytes.Road.K4 (ents_front ents_back)
open OnBytes.Road.K4.InT (kept_open)
open Fo.Tp (bare_ents)

variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)

/-- **JLay2 from KeptAt, PadAt and the lines.** -/
theorem jLay2_of_kept (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (hLines : ∀ g hp, XV.G[g]? = some hp → LayLines XV g hp) (l : ℕ) (hl : l < 25)
    (hsub : (linksFull[l]?).getD .layers = ModelPart.layers) {s : S} (K : KeptAt Bs.G₀.W (l / 2) s)
    (hPad : PadAt s) : JLay2 Dm s := by
  obtain ⟨el, hg12⟩ := layIsEven l hl hsub
  have hno : linkNo s = l := by
    obtain ⟨_, _, _, _, _, _, _, hln⟩ := K
    unfold lnOf at hln
    unfold linkNo
    rw [hln, ← el]
    rfl
  intro b₀ o hp A₁ hs ho hg hA
  rw [hno] at hg
  have hgW : Bs.G₀.W.G[l / 2]? = some hp := by rw [hWX]; exact hg
  refine ⟨u3_of_kept K hs ho hgW, ?_⟩
  rw [hno]
  intro p e cc hrun hN
  obtain ⟨j, n, hi, hpr⟩ := hrun
  have hpr' : p ∈ runsAt linksFull l j n := by
    have e0 : Dm.runs l j n = runsAt linksFull l j n := by
      show runsAt Dm.links l j n = _
      rw [hDlk]
    rw [← e0]
    exact hpr
  have t := List.all_eq_true.1 layRuns l (List.mem_range.2 hl)
  rw [hsub] at t
  have t1 := List.all_eq_true.1 (List.all_eq_true.1 (show _ = true from t) _ hi) p hpr'
  obtain ⟨R, f, hRf, hf, he, _, _, _⟩ := hN
  obtain ⟨Lk, b, x, e1, e2, _, hla, _, xg, xP, xh, _⟩ := IM.k4_of hS hR O (l / 2) hg12
  rw [← el] at e1
  have hRd : Dm.Rd l = readersOfLink (holesAt XV (headLink XV) l Lk) Lk :=
    K9.readersAt_some Dm.lk XV (headLink XV) l Lk ((hlk l hl).trans e1)
  have hne : (l == headLink XV) = false := by
    rw [hX24]
    exact beq_false_of_ne (by omega)
  rw [hRd] at hRf
  have hst : statesOfLink Lk 2 = (blockAtC { x.2 with k3Runs := true }).claims.map
      fun c => (c.1, IM.guardRun ProofFile.sameReply c.2) := by
    unfold statesOfLink
    rw [e2, Option.map_some, Option.getD_some, IM.claims_alone hla]
    rfl
  obtain ⟨pk, s₀, Kk, pg, pP, ph, _, _⟩ := K
  obtain ⟨a, fo, o', G, ha, hfo, _, _, h5, _, _, _, hRest, hofo, _, tt, u, hh⟩ := Kk
  obtain ⟨a'', ha'', _, efo, _, _⟩ := hRest.here a ha
  obtain rfl : b₀ = a'' := First.Here.lay.inj (hs.symm.trans ha'')
  obtain rfl : o = o' := by
    have e0 : s.own? = b₀.own := by simp [S.own?, hs]
    exact Option.some.inj (ho.symm.trans (e0.symm.trans h5))
  obtain rfl : pk.hp = hp := Option.some.inj (ph.symm.trans hgW)
  obtain ⟨F', N0⟩ := hPad.1 b₀ fo hs (efo.trans hfo)
  have N : Fo.Tp.PadNames o.H.fo F' := by rw [hofo]; exact N0
  have Ln := hLines (l / 2) pk.hp hg
  obtain ⟨-, -, iU3, _, _, _, _, _, _, _, e3, -, -, -, ev, -⟩ :=
    OnBytes.Desc.First.K4.hear_public
      (show OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl _ pk.hp pk.g fo a.F tt =
        some (o, G, u) from hh)
  have hu : u3Of pk.hp.tl = iU3 := by
    unfold u3Of
    rw [e3]
    rfl
  have hK : pk.hp.nU.getD 2 0 ≤ o.v.K3 := by
    rw [ev]
    show _ ≤ ((pk.hp.Fp.trees[iU3]?).map (·.K)).getD 0
    rw [← hu]
    exact Ln.hK
  have hm : ((({ pk.P with tokv := s₀.tokv } : Layer.Pub).tails.getD pk.g {}).mats.map
      fun M => (M.m, M.k)) = OnBytes.Road.matsR ({ pk.P with tokv := s₀.tokv } : Layer.Pub).y pk.g := by
    show ((pk.P.tails.getD pk.g {}).mats.map fun M => (M.m, M.k)) = OnBytes.Road.matsR pk.P.y pk.g
    rw [pP, pg, hWX]
    exact Ln.hm
  have hgN : pk.g < ({ pk.P with tokv := s₀.tokv } : Layer.Pub).y.NGr := by
    show pk.g < pk.P.y.NGr
    rw [pP, pg, hWX]
    exact Ln.hg
  have htm : (pk.hp.tl.mats.map fun M => (M.m, M.k)) =
      OnBytes.Road.matsR ({ pk.P with tokv := s₀.tokv } : Layer.Pub).y pk.g := by
    show _ = OnBytes.Road.matsR pk.P.y pk.g
    rw [pP, pg, hWX]
    exact Ln.htm
  simp only [Bool.or_eq_true, beq_iff_eq] at t1
  rcases t1 with ((rfl | rfl) | rfl) | rfl
  · have hr := reader_of_forms hne Lk (by decide) hRf
    obtain ⟨ff, G₁, hfr, eR⟩ := forms_of_reader (block_front seatOwn _) hst hs ho hr
    rw [frontOf_eq] at hfr
    have hf0 : formsFrontWith false { pk.P with tokv := s₀.tokv } pk.g o b₀.F = some (ff, G₁) := by
      have e := run_pub false pk.P { pk.P with tokv := s₀.tokv } pk.g o b₀.F rfl rfl
      rw [e, pP, pg, ← xP, ← xg]
      exact hfr
    obtain ⟨r1, r2, _, r4⟩ := ents_front hh hK N hf0 pk.hp.tl hm hgN htm Ln.hNM f
      (by rw [← eR]; exact hf) e he
    exact ⟨r1, r2, r4⟩
  · have hr := reader_of_forms hne Lk (by decide) hRf
    obtain ⟨ff, G₁, hfr, eR⟩ := forms_of_reader (block_back seatOwn _) hst hs ho hr
    obtain ⟨r1, r2, _, r4⟩ := ents_back hh hK N (bare_ents N0.cEnd.1) hfr pk.hp.tl hm hgN htm
      Ln.hNM f (by rw [← eR]; exact hf) e he
    exact ⟨r1, r2, r4⟩
  · exfalso
    have hr := reader_of_forms hne Lk (by decide) hRf
    have hb := reader_bare (statesOfLink Lk) 1 "objects"
      (states1_bare hS hR O l (by omega) Lk e1 "objects" (by decide)) hPad.2 hr f hf
    rw [hb] at he
    cases he
  · exfalso
    have hr := reader_of_forms hne Lk (by decide) hRf
    have hb := reader_bare (statesOfLink Lk) 1 "guests"
      (states1_bare hS hR O l (by omega) Lk e1 "guests" (by decide)) hPad.2 hr f hf
    rw [hb] at he
    cases he

/-- **THE CLAUSE, ALONG "REACHED", IN FRONT OF EACH LINK's READS**: in hJ's own letters. -/
theorem jLay2_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX24 : headLink XV = 24) (hWX : Bs.G₀.W = XV)
    (hLines : ∀ g hp, XV.G[g]? = some hp → LayLines XV g hp) {W : Type} {Fr : Frame} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W)
    (hPad : ∀ l, l < 25 → (linksFull[l]?).getD .layers = ModelPart.layers →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → PadAt a.1.2) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → JLay2 Dm a.1.2 := by
  intro l hl a hr hon hm
  by_cases hsub : (linksFull[l]?).getD .layers = ModelPart.layers
  · exact jLay2_of_kept Dm hS hR O hDlk hlk hX24 hWX hLines l hl hsub
      (kept_at_reads hS hR O l hl hsub a hr) (hPad l hl hsub a hr hon hm)
  · intro b₀ o hp A₁ hs
    exfalso
    have hst := stand_of_promise l hl a.1 _ ⟨hon, hm⟩
    unfold First.standOf at hst
    rw [hs] at hst
    exact hsub (First.Stand.link.inj hst).symm

end

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.layRuns
#print axioms VerifiableInference.Desc.K1.layRuns_fails
#print axioms VerifiableInference.Desc.K1.reader_of_forms
#print axioms VerifiableInference.Desc.K1.states1_bare
#print axioms VerifiableInference.Desc.K1.jLay2_of_kept
#print axioms VerifiableInference.Desc.K1.jLay2_at_reads
