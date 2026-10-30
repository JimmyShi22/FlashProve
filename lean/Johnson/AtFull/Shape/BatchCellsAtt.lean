-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchCellsAtt.lean: THE TWELVE ATTENTION LINKS' BATCHING MEMBERS OF THE PROOF
FILE's OWN FIRST CHAIN: the slot of the lookup's run "planes" there; the link's ten rows as plain
functions of the public record; and "carries" WITH THE VALUES IN HAND, AND Returns, at these twelve
members. With BatchCells.lean: ALL 25 BATCHING MEMBERS. A joining of laws; nothing is evaluated. The
law of "planes" at the attention links is two other houses'
(Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanes.lean;
Johnson/Desc/ProofFile/Honest/K5/Law/RunsPlanes.lean).

  **`k3_planes_att`** (g < 12): Bs by baseOf's value · Lk by cF.links[2 g + 1]? · A by Bs.G₀.W.A[g]?
    · q by placeAt Bs.G₀.W (2 g + 1) false: SlotAt at (1, "planes"): planesRun (seatCalls
    K3Lot.ofForm) q.lm (P.readersOfO A) · planesShG q.lm (k5ReadersG A) · fun _ s => valsTS A s.
  **`rowsAtt A lm`**: the ten rows of an attention link.
  **`att_batch`** (g < 12): for every ft, G with G (14 (2 g + 1) + Lk.hear.length + 2) =
    cellG p w.1 (rowsAtt A q.lm) Lk.order and vals with vals ‹number› = cellV p (rowsAtt A q.lm)
    Lk.order: CarriesV and Returns at that member.

Limits. att_batch does not say that a member stands at its number; number, step and Bool still hang
on the link Lk (Lk.hear.length, Lk.order), tied by cF.links[2 g + 1]? alone. CarriesV is the frame's
house's CarriesU, written out, not Carries. In cellV a clause is true where no ledger is open, where
the draw refuses, and for the runs behind one that refuses (BatchTerms.lean's batchVT). That cellV
accepts at a state of a run, and that cellG returns at a shape that the chain reaches, are not
shown. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchCells
import Johnson.Desc.ProofFile.Honest.K5.Law.RunsPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Att (P.readersOfO P.parCOf)
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where)
open VerifiableInference.Desc.K3 (seatCalls planesRun)
open ProofFile.Honest.K3.Shape (planesShG planesRun_reply planesRun_st)
open H2K5.Honest (k5ReadersG planesLawA planesA_pre valsTS)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)
open ProofFile.Honest (Returns)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k3_planes_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (A : Attention.Plan)
        (q : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[2 * g + 1]? = some Lk ∧ Bs.G₀.W.A[g]? = some A ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some q ∧
      SlotAt Lk.hear (1, "planes") (planesRun (seatCalls K3Lot.ofForm) q.lm (P.readersOfO A))
        (planesShG q.lm (k5ReadersG A)) (fun _ s => valsTS A s) := by
  have hl : 2 * g + 1 < 25 := by omega
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have i1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, h24]
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, -, -, hA⟩ := Meaning.scope_plans h.scope h.reads O.public
  obtain ⟨A, eA, -⟩ := hA g hg
  obtain ⟨Lk, b, b', eL, eb, hst, hla⟩ := IM.k3_of h.scope h.reads O (2 * g + 1) hl false
  rw [i1] at eb
  have hs : Lk.hear[1]? = some (IM.seatedAs ProofFile.sameReply b' b.name
      (IM.k3Place (2 * g + 1) false)) := eb.trans (congrArg some hla)
  obtain ⟨i, d, hi, hp⟩ := stated_piece hst
  obtain rfl : 2 * g + 1 = i := Option.some.inj hi
  obtain ⟨rfl, hH⟩ := piece_tells Bs.G₀.W (2 * g + 1) false d hp
  have hnH : ¬ VerifiableInference.Desc.K3.isHead Bs.G₀.W (2 * g + 1) = true :=
    fun e => h24 (hH.1 e)
  have hr : K3Lot.readersAt Bs.G₀.W (2 * g + 1) = some (P.readersOfO A) := by
    unfold K3Lot.readersAt
    rw [if_neg hnH]
    have e2 : (if Bs.G₀.W.p4 = true then 2 else 1) = 2 := by rw [h4]; rfl
    simp only [e2]
    have e3 : ((2 * g + 1) % 2 == 0) = false := by
      have : (2 * g + 1) % 2 = 1 := by omega
      rw [this]
      rfl
    have e4 : (2 * g + 1) / 2 = g := by omega
    rw [e3, e4, eA]
    rfl
  obtain ⟨q, b₀, h1, h2, h3⟩ := VerifiableInference.Desc.K3.theStated_planes K3Lot.ofForm _ _ _ _ _
    b' hst (2 * g + 1) _ hi hp hr
  obtain ⟨tail, ht⟩ := VerifiableInference.OnPublicFiles.theWhole_twoAt K3Lot.ofForm _ _ _ _ b₀ h2
    (2 * g + 1) false hi hp
  have hn := (VerifiableInference.Desc.K3.theWhole_names K3Lot.ofForm _ _ _ _ b₀ h2).1
  have htl : tail = [] := by
    rw [ht] at hn
    simpa using hn
  refine ⟨Bs, Lk, A, q, O.made, eL, eA, h1,
    { lot := b', name := b.name, place := IM.k3Place (2 * g + 1) false, seated := hs
      bare := planesRun (seatCalls K3Lot.ofForm) q.lm (P.readersOfO A)
      states := by rw [h3, ht, htl]; rfl
      law := planesLawA A q.lm
      keeps := fun n s s' cs hr => planesRun_reply q.lm _ n s (cs, s') hr
      still := fun n s s' cs hr => planesRun_st q.lm _ n s (cs, s') hr }, rfl, rfl,
    ⟨fun _ s => valsTS A s, fun n s hv => planesA_pre A q.lm n hv⟩, rfl⟩

/-- **The ten rows of an attention link.** -/
def rowsAtt (A : Attention.Plan) (lm : Nat) : List ((Nat × String) × Row) :=
  [((1, "objects"), rowObjects false), ((1, "guests"), rowGuests),
   ((2, "first"), ⟨K5Law.runFirst (P.parCOf A), H2K5.Honest.k5FirstG A, fun _ s => valsTS A s⟩),
   ((2, "keys"), ⟨K5Law.runKeys (P.parCOf A), H2K5.Honest.k5KeysG A, fun _ s => valsTS A s⟩),
   ((2, "join"), ⟨H2K5.Honest.joinRunA A, H2K5.Honest.k5JoinG A, fun _ s => valsTS A s⟩),
   ((2, "second"),
     ⟨K5Law.runSecond (P.parCOf A), H2K5.Honest.k5SecondG A, fun _ s => valsTS A s⟩),
   ((1, "planes"),
     ⟨planesRun (seatCalls K3Lot.ofForm) lm (P.readersOfO A), planesShG lm (k5ReadersG A),
      fun _ s => valsTS A s⟩),
   ((6, "objects"), rowObjects true), ((6, "guests"), rowGuests), ((4, "K8.equations"), rowEq)]

theorem att_batch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere)
        (A : Attention.Plan) (q : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[2 * g + 1]? = some Lk ∧ IM.k9At Zp (2 * g + 1) = some p ∧
      testsWhere Zp.p.X (2 * g + 1) 0 = some w ∧ Bs.G₀.W.A[g]? = some A ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some q ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * (2 * g + 1) + Lk.hear.length + 2) = cellG p w.1 (rowsAtt A q.lm) Lk.order →
        vals (14 * (2 * g + 1) + Lk.hear.length + 2) = cellV p (rowsAtt A q.lm) Lk.order →
        CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * (2 * g + 1) + Lk.hear.length + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * (2 * g + 1) + Lk.hear.length + 2) := by
  have hl : 2 * g + 1 < 25 := by omega
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hsub : subAt (2 * g + 1) = .attention := by
    unfold subAt
    rw [if_neg h24, if_neg (by omega)]
  have i1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, h24]
  have i6 : IM.k3Ix (2 * g + 1) true = 6 := by simp [IM.k3Ix, h24]
  obtain ⟨Lk, p, w, eL, hp, hw, hN⟩ := batch_of_tables h (2 * g + 1) hl
  obtain ⟨L1, _, _, _, e1, _, _, _, hord, _⟩ := batch_named h (2 * g + 1) hl
  obtain rfl : Lk = L1 := Option.some.inj (eL.symm.trans e1)
  obtain ⟨Bs, L5, A, hB, e5, hA, s1, s2, s3, s4⟩ := k5_slotAt h g hg
  obtain rfl : Lk = L5 := Option.some.inj (eL.symm.trans e5)
  obtain ⟨Bp, Lp, Ap, q, hBp, ep, hAp, hq, spl⟩ := k3_planes_att h g hg
  obtain rfl : Bs = Bp := Except.ok.inj (hB.symm.trans hBp)
  obtain rfl : Lk = Lp := Option.some.inj (eL.symm.trans ep)
  obtain rfl : A = Ap := Option.some.inj (hA.symm.trans hAp)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h (2 * g + 1) hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h (2 * g + 1) hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h (2 * g + 1) hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i1] at sao sag
  rw [i6] at sbo sbg
  refine ⟨Bs, Lk, p, w, A, q, hB, eL, hp, hw, hA, hq, fun ft G vals hG hv =>
    hN (fun o => (tabOf (rowsAtt A q.lm) o).run) (fun o => (tabOf (rowsAtt A q.lm) o).g)
      (fun o => (tabOf (rowsAtt A q.lm) o).pre) ?_ ft G vals hG hv⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact spl
  · exact sbo
  · exact sbg
  · exact s8

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k3_planes_att
#print axioms Johnson.AtFull.Shape.att_batch
#print axioms Johnson.AtFull.Shape.rowsAtt
