-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05OwF.lean: K05_law at the library's letters: what the score at the index
owes at the
chain's end (the letter owF), cancelled against the kind's own claims. General in the readers'
forms.

Main names:
  `sumAt_lenV`: a sumcheck has heard as many end values as its stage says.
  `value_owF`: where the row of the score at the index is worth 0 in the ledger's world and the slot
    of its
    end value number 2 b is worth the reader's form number b (both are what the kind's gathered
      claims say):
    owF holds exactly if, for every pair b, the typed first map of pair b at the output's point is
      what that
    form is worth. The second end values have no claim at the end: they are the start of the key's
      sumcheck.

Premises: Said, TailOfP · the library's numbering sc3Num · (D1) · the places of the pairs' scalars'
mask entries
and of the first end values' · the place's two numbers are the description's · PartRowLaw.
Sources: what Att/K05Prem.lean and Att/K5Mean.lean name; Cb/Pv/Att/OwnSteps.lean (iB).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Prem
import Johnson.Desc.First.Att.K5Mean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

theorem sumAt_lenV {C : Aff} {vs : List MaskedSum.Var} {e : MaskedSum.Ends} {pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (.sum vs e) pre H hh G) : H.v.length = e.n := by
  obtain ⟨vs', e', F, G0, used, e1, sd, _⟩ := h
  injection e1 with _ e3
  rw [e3]
  exact sd.lenV

variable (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap)

/-- **What the score at the index owes, where K5's claims hold.** -/
theorem value_owF (law : MaskedSum.PartRowLaw) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (hs : Said (recOf P rows) h G L) (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail)
    (hnF : ∀ a : Fin P.D.nb × Bool, nm.nF a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT)
    (g2 : g.lgk = P.D.lg) (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff} (hf : left G h.atIndex (wAtIndex g h) = some f)
    (hkF : ∀ i : Fin P.D.nb, P.msg m (P.kF i) = mask (h.maxima + i.1))
    (hmF : ∀ b : Fin P.D.nb, P.msg m (P.cAt .s16 (b, false)) = mask (h.atIndex.sEnd + 2 * b.1))
    (D1 : (P.st3 .s16 fun p => incAt P.kF fun b => p.o b).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dF.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot
        ((P.st3 .s16 fun p => incAt P.kF fun b => p.o b).plain.our.par.vars
          (tailData (P.tail Mn).toTail L h nz nm x0).dF.st) h.atIndex.first)
    (reader : ℕ → Aff) (hrow : f.value ρ (G.worldOf ρ mask entry) = 0)
    (hslots : ∀ b < P.D.nb, (G.worldOf ρ mask entry).slot (h.atIndex.sEnd + 2 * b) =
      (reader b).value ρ (G.worldOf ρ mask entry))
    (y : (((P.tail Mn).toTail.sVD.Nx × (Fin (P.tail Mn).toTail.nz → K)) × (Fin (P.tail Mn).toTail.np → K)) × K) :
    (P.tail Mn).toTail.owF ((tailData (P.tail Mn).toTail L h nz nm x0).dF.nx y) m ↔
      ∀ b : Fin P.D.nb, P.sF.T.map (tailData (P.tail Mn).toTail L h nz nm x0).dF.st (P.msg m) (b, false)
        (ldPartIni P.sF.T.nv P.sF.T.deg (pDummy K P.sF.T.DY) (tailData (P.tail Mn).toTail L h nz nm x0).dF.out.pt) =
          (reader b.1).value ρ (G.worldOf ρ mask entry) := by
  have hp := value_atIndex_prem P Mn rows hs nz nm hnF x0 g g1 g2 ho mask entry m hf hkF D1
  rw [owF_iff law (P.tail Mn) _ ho.zF ho.oF hs.sF hp y]
  have hlen : L.HF.v.length = 2 * P.D.nb := sumAt_lenV hs.sF
  have hend : ∀ b : Fin P.D.nb,
      (P.tail Mn).toTail.sF.T.our.par.EHolds (tailData (P.tail Mn).toTail L h nz nm x0).dF.out
          ((P.tail Mn).toTail.sF.msg m) (b, false) ↔
        P.sF.T.map (tailData (P.tail Mn).toTail L h nz nm x0).dF.st (P.msg m) (b, false)
          (ldPartIni P.sF.T.nv P.sF.T.deg (pDummy K P.sF.T.DY)
            (tailData (P.tail Mn).toTail L h nz nm x0).dF.out.pt) = (reader b.1).value ρ (G.worldOf ρ mask entry) := by
    intro b
    have he := end_slot (P.tail Mn).toTail.sF (tailData (P.tail Mn).toTail L h nz nm x0).dF ho.oF hs.sF m (b, false)
      (2 * b.1) (by rw [hlen]; have := b.2; omega) mask entry
      (by
        show ρ.val (L.HF.v.getD (nm.nF (b, false)) zeroE) = _
        rw [hnF]
        simp [sc3Num])
      (hmF b)
    rw [hslots b.1 b.2] at he
    exact he
  constructor
  · rintro ⟨_, H⟩ b
    exact (hend b).1 (H (b, false) fun i hi => by
      have := congrArg Prod.snd hi
      simp [OwnPar.tail, OwnPar.iB] at this)
  · intro H
    refine ⟨hrow, fun a ha => ?_⟩
    obtain ⟨b, c⟩ := a
    cases c with
    | false => exact (hend b).2 (H b)
    | true => exact absurd rfl (ha b)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.value_owF
