-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/K4TextsHanded.lean: THE JOIN WITH THE FEED-FORWARD LAYERS' HOUSE: ITS TWO THEOREMS
`k4_live4_fits`, `k4_un4_fits` (Honest/K4/Law/Live/GoodLayFormFits.lean), WHOSE ENDS ARE THE PREMISES live4 AND un4 OF
OUR `liveLayers_of_clauses` (Honest/K9/GoodLayLive.lean), CALLED AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF
A FEED-FORWARD SEGMENT's BATCHING. These two have 16 and 9 named hypotheses, eighteen distinct. FIFTEEN ARE PAID FROM
THE WALK (hC AMONG THEM, BY THAT HOUSE's `k4_coin_of_yes`: FROM K4's OWN ACCEPTANCE); hM FROM THE PREMISE hsub4; hll,
hLam ARE ASKED: THREE PREMISES (and hhp, public: which plan stands at g). Statements and proofs; no definition; no goal
is stated.
  `words_of_drawsFit`   challenges that a list of rounds can draw (the frame's `drawsFit`) have every word of every
      element below the prime · `k4CoinZero_blind`: K4's fall's test reads of the place's public data the layers' data,
      the plan and the group alone (by unfolding): so the letters r0 and sg below are idle where that test is spent; in
      hsub4 they are idle by `k4MarkWide_blind`
  **`k4_texts_handed`**   under the head · hB · hC (the calls' public place) · the lookups' marks and the fit's among
      the marks asked · the walk's premises at A.length = 14 (2 g) + 9 · AND THREE: hsub4: K4's wider mark at ⟨the
      layers' public data, hp, g, 2 g, 3, r0, sg⟩ is among the marks asked (hp: the plan's own at g; r0, sg: letters) ·
      hll, hLam: two public numbers of the layers' data. THE END: some p4, a, a₀, fo, o, hsC with: p4 is K4's parameters
      at 2 g · s' stands at a₀, which holds o and, as heard by the calls' lookup, fo · hsC is the calls' shape, and a's
      ledger's next slot is the end of the calls' stretch, WHICH LIES AT OR BELOW THE SLOT OF THE MERGE's END VALUE
      (o.wo.sFv) · `K4.Live4Text p4 a₀ (k4W4 a.F.next fo a₀)` · `K4.Un4Text p4 s' a₀ n`
WHO PAYS WHAT. `k4_front_handed` (Honest/K9/LayFrontHanded.lean): h · eP, ehp, eg (from three equations) · ha · hfo · hF
· N · hs · hcar · that house's `k4_hrf_of_step` at "declares": hrf · the fit's mark's silence and `words_of_drawsFit`:
hw · hsub4 and `mark_silent`: hM · the lookups' house's `free_behind_calls`: hfree · its `leaves_below` at the clause
that the smallness test's house's `clause_at_step` hands, with that lemma's second half: hlv · the feed-forward layers'
house's `k4_coin_of_yes` (Honest/K4/Law/Live/CoinOfYes.lean) at h: hC · its `k4_next_le_of_yes` (NextAtYes.lean): the
end's inequality.
WHAT IS NOT CLAIMED. The three premises at anything. THE EVENT OF hC IS NOT SAVED 
: it has moved into K4's acceptance, itself an event on K4's challenges, which the walk's return
holds: where the element is 0 there is no acceptance, and this theorem is silent there: WHOEVER SUMS SHARES MAY NOT DROP
K4's FALL's ON THE STRENGTH OF THIS FILE. That K4's wider marks stand in any list of marks. That any walk returns. No
member. Called by Honest/K9/BatFrontHandedK4.lean alone; `words_of_drawsFit` by this file alone; `k4CoinZero_blind` by
no line. At the full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file lie 396 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.LayFrontHanded
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.GoodLayFormFits
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.CoinOfYes
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.NextAtYes
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.FreeAt
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Forms
import Johnson.P1K8R.ClausesAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark markOf marksQuiet mark_silent drawsFit drawFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K3.Good.Live (Clause leaves_below free_behind_calls)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty)
open ProofFile.Honest.K4 (k4MarkWide k4CoinZero)
open ProofFile.Honest.K4.Live (k4W4 k4_live4_fits k4_un4_fits k4_coin_of_yes k4_next_le_of_yes)
open OnBytes.Desc.First.K4.Honest (K4Pub)

/-- Challenges that a list of rounds can draw have every word of every element below the prime. -/
theorem words_of_drawsFit : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), drawsFit ds Rs = true →
    ∀ R ∈ Rs, ∀ x ∈ R.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord
  | [], [], _, R, hR, _, _ => absurd hR (List.not_mem_nil)
  | [], _ :: _, h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _, _, _ => by simp [drawsFit] at h
  | d :: ds, R₀ :: Rs, h, R, hR, x, hx => by
    unfold drawsFit at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hR with rfl | hm
    · have h1 := h.1
      unfold drawFit at h1
      simp only [Bool.and_eq_true] at h1
      have k := List.all_eq_true.1 h1.1.2 x hx
      simpa [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using k
    · exact words_of_drawsFit ds Rs h.2 R hm x hx

/-- K4's fall's test reads of the place's public data the layers' data, the plan and the group alone. -/
theorem k4CoinZero_blind (P : Layer.Pub) (hp : Layer.HPlan2) (g l c a s l' c' a' s' : ℕ) :
    k4CoinZero ⟨P, hp, g, l, c, a, s⟩ = k4CoinZero ⟨P, hp, g, l', c', a', s'⟩ := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **THE FEED-FORWARD LAYERS' HOUSE's TWO TEXTS (live4 AND un4 OF `liveLayers_of_clauses`) AT THE STATES THAT THE
FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING**, at that house's own set of slots `k4W4`. -/
theorem k4_texts_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12)
    {pC : Look.P} (hC : Look.placeAt (P5J.At.X Zp) (2 * g) false = some pC)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {hp : Layer.HPlan2} (hhp : Bs.G₀.W.G[g]? = some hp) (r0 sg : ℕ)
    (hsub4 : k4MarkWide ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ ∈ ms)
    (hll : Bs.G₀.W.layers.y.h.ll - 1 = 1) (hLam : Bs.G₀.W.layers.y.LamM ≤ 2)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {w₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok w₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr w₀ = .ok z) (hv : z.ver = some s') (n : ℕ) :
    ∃ (p4 : OnBytes.Desc.First.K4.Par) (a a₀ : LayOwn) (fo : Forest.Heard) (o : Layer.Own) (hsC : Forest.Shape),
      LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4 ∧ s'.here = .lay a₀ ∧ a₀.own = some o ∧
      a₀.lookHeard = some fo ∧ pC.shape = some hsC ∧ a.F.next = pC.first + Forest.elems hsC ∧
      pC.first + Forest.elems hsC ≤ o.wo.sFv ∧
      K4.Live4Text p4 a₀ (k4W4 a.F.next fo a₀) ∧ K4.Un4Text p4 s' a₀ n := by
  obtain ⟨blk, b₄, sj, sk, sm, R, R₂, cs, d₂, f₁, f₂, p4, a, a₀, fo, o, hb₁, f4, g3, hs1, k3, hs2, hrk, e4, eP', eh',
    eg', hpl, hdecl, hrf0, hd, hask, hfo, hlk, hF, N, hsm, ha₀, hoa, hcar, hlk'⟩ :=
    k4_front_handed h hB hg ms hall hfit hA hpos L hft hm ha hn hq hz hv
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  have n24 : ¬ 2 * g = 24 := by omega
  have inA : ∀ {i : ℕ} {d : Block S ProofFile.Cl}, i < 14 * (2 * g) + 9 → cF.blocksInOrder[i]? = some d → d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  -- the public letters
  have eP : (⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ : K4Pub).P = p4.P := eP'.symm
  have ehp : (⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ : K4Pub).hp = p4.hp :=
    Option.some.inj (hhp.symm.trans eh')
  have eg : (⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ : K4Pub).g = p4.g := eg'.symm
  -- K4's rounds: they fit the written entries; their words are below the prime; K4's mark is silent
  have hrf := ProofFile.Honest.K4.Live.k4_hrf_of_step k3 hdecl _ eP ehp eg
  have hdf := P1K8.fit_at_silent b₄ (hfit b₄ (inA (by omega) f4)) hs2
  have hw : ∀ q ∈ R₂, ∀ y ∈ q.drawn.elems, y.1 < fieldPrimeWord ∧ y.2.1 < fieldPrimeWord ∧ y.2.2 < fieldPrimeWord :=
    fun q hq' y hy => words_of_drawsFit _ _ hdf q.drawn (List.mem_map_of_mem hq') y hy
  have hM : (k4MarkWide ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩).test f₂ (R₂.map (·.drawn)) = none :=
    mark_silent hsub4 (by
      show (markOf ms (⟨1, some (2 * g), 3, .K4⟩ : Place) f₂ (R₂.map (·.drawn))).isSome = false
      rw [show (⟨1, some (2 * g), 3, .K4⟩ : Place) = b₄.place from hpl.symm, hs2]
      rfl)
  have hCz : k4CoinZero ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ (R₂.map (·.drawn)) = none :=
    k4_coin_of_yes hd _ eP eg _ (fun i => by
      rw [List.getElem?_map, List.getElem?_map, Option.map_map, Option.map_map]
      rfl)
  -- K4's hearing begins at or below the slot of the merge's end value
  obtain ⟨o', G₄, esm, hle, -⟩ := k4_next_le_of_yes hd hask hF
  obtain rfl : o' = o := by
    have k : sm.own? = some o' := by
      rw [esm]
      rfl
    exact Option.some.inj (k.symm.trans hsm)
  -- nothing is filled from the ledger's next slot on
  have hGa : sk.fork? = some a.F := by simp [S.fork?, hask]
  obtain ⟨-, Rr, Cc, hf0⟩ := hrk.fold
  have i3 : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg n24]
    rfl
  obtain ⟨G, hG, -, hfree⟩ := free_behind_calls h.scope h.reads O h.laid.planOk (2 * g) (by omega)
    (s₀ := ProofFile.startS Zp zp) (t := sk) (R := Rr) (R' := []) (C := Cc) (C' := []) (by
            rw [i3]
            exact hf0)
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans hGa)
  -- the calls' lookup: its clause, and where the ledger's next slot stands behind it
  obtain ⟨s, hs, el, hdg, -, -⟩ := site_at_all_fifty h (2 * g) (by omega) false
  obtain rfl : s.p = pC := by
    have k := (P1K8.site_pars s hs).1
    rw [el, hdg] at k
    exact Option.some.inj (k.symm.trans hC)
  have spC := (P1K8.site_pars s hs).2
  have hbC : borderOf (2 * g) false = 14 * (2 * g) + 3 := by
    rw [P1K8.border_calls, if_neg n24]
  obtain ⟨JC, G', hG', hnext⟩ := P1K8.clause_at_step h G₀ s hs (by omega) (blk := blk) (by
    rw [el, hdg, hbC]
    exact hb₁) ms hsub (hfit blk (inA (by omega) hb₁)) g3 hs1
  rw [hdg] at JC
  obtain rfl : G' = a.F := Option.some.inj (hG'.symm.trans hGa)
  obtain ⟨H, eH, JH⟩ := JC
  obtain rfl : H = fo := Option.some.inj ((show sk.lookHeard? = some H from eH).symm.trans hlk)
  have hlv : H.leaves.first + H.leaves.walk.1.length ≤ a.F.next := by
    rw [hnext]
    exact leaves_below spC (⟨H, rfl, JH⟩ : Clause s.p (some H))
  refine ⟨p4, a, a₀, H, o', s.shape, e4, ha₀, hoa, hlk', spC, hnext, hnext ▸ hle, ?_, ?_⟩
  · exact k4_live4_fits hd _ eP ehp eg hrf hw hM hCz hask hfo hF hfree N (by rw [eP']; exact hll)
      (by rw [eP']; exact hLam) a₀ hcar
  · exact k4_un4_fits hd hask hfo hF hfree N hlv s' a₀ n ha₀ hcar

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.words_of_drawsFit
#print axioms ProofFile.Honest.K9.k4CoinZero_blind
#print axioms ProofFile.Honest.K9.k4_texts_handed
