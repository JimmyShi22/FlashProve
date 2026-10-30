-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SlotsAt.lean: (D1) in the ledger's world, at all letters of a sumcheck,
from the
places alone.

Main names:
  `degSum_plain`: a plain sumcheck's formats' degrees sum to its variables' degrees and DY.
  `coef_put`: under the slot of the coefficient named i lies 0, with the factor -1.
  `D1_at`: for letters with the script's sizes and a sumcheck seen from a ledger: if the entry at
    which the
    letters lay the coefficient named i is the mask at slot posP … first i, then (D1) holds in that
      ledger's
    world.
  `put_lt`: a slot under which something lies is one of the ledger's.

Sources: what Att/K05Slots.lean and Att/K5HearLaw.lean name; Cb/Part/LdPartVars.lean (ldPartFmt);
pDummy.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Slots
import Johnson.Desc.First.Att.K5HearLaw
import Johnson.Desc.First.Att.K5Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

theorem degSum_plain (DY : ℕ) : ∀ (k : ℕ) (deg : Fin k → ℕ),
    degSum (ldPartFmt K k deg ++ [pDummy K DY]) = (List.ofFn deg).sum + DY
  | 0, _ => by simp [ldPartFmt, degSum, pDummy]
  | k + 1, deg => by
    show deg 0 + degSum (ldPartFmt K k (fun i => deg i.succ) ++ [pDummy K DY]) = _
    rw [degSum_plain DY k, List.ofFn_succ, List.sum_cons]
    omega

/-- Under the slot of the coefficient named i lies 0, with the factor -1. -/
theorem coef_put {X : Type} (S : SumL K M X) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (h : SumAt C st riders H hh Gf)
    (i : PIdx (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY])) :
    Put Gf (posP (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY]) hh.first i) zeroE (subE zeroE oneE) := by
  obtain ⟨vs, e, F, G, used, e1, sd, hst⟩ := h
  obtain ⟨n, e2⟩ := hs
  rw [e1] at e2
  injection e2 with e3 e4
  subst e3 e4
  have hb := posP_lt (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY]) hh.first i
  rw [degSum_plain] at hb
  have hlen : (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length = 1 + ((List.ofFn S.T.deg).sum + S.T.DY) := by
    have hz1 : (hh.vars.zip hh.r).map (·.1) = hh.vars := by
      refine List.map_fst_zip ?_
      rw [sd.vars, sd.r]
      have := congrArg List.length sd.lens
      simp at this ⊢
      omega
    rw [hiding_length _ (fun h0 => by
        rw [h0] at hz1
        rw [sd.vars] at hz1
        simp at hz1) (fun x hx => by
        have hm : x.1 ∈ hh.vars := by
          rw [← hz1]
          exact List.mem_map_of_mem hx
        rw [sd.vars] at hm
        rcases List.mem_append.1 hm with h1 | h1
        · obtain ⟨d, _, hd⟩ := List.mem_map.1 h1
          rw [← hd]
          show 1 ≤ d + 1
          omega
        · rw [List.mem_singleton.1 h1]
          show 1 ≤ S.T.DY + 1
          omega), hz1, sd.vars]
    unfold MaskedSum.ownSlots
    rw [own_fold, List.map_append, List.sum_append, List.map_map]
    have : ((fun x : Var => x.d - 1) ∘ fun d => Var.plain (d + 1)) = id := by
      funext d
      show d + 1 - 1 = d
      omega
    rw [this, List.map_id]
    show 1 + ((List.ofFn S.T.deg).sum + (S.T.DY + 1 - 1 + 0)) = _
    omega
  obtain ⟨k, hk⟩ : ∃ k, posP (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY]) hh.first i = hh.first + k :=
    ⟨_, (Nat.add_sub_of_le hb.1).symm⟩
  rw [hk]
  exact hst _ _ _ (sd.coefs k (by rw [hlen]; omega))

/-- **(D1) in the ledger's world, from the places.** -/
theorem D1_at {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (h : SumAt C st riders H hh Gf)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M)
    (hw : ∀ i, S.msg m (S.T.wAt i) = mask (posP (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY]) hh.first i)) :
    S.T.our.par.W D.st (S.msg m) =
      OnBytes.Road.Hd.place (Gf.worldOf ρ mask entry).slot (S.T.our.par.vars D.st) hh.first := by
  refine D1_of_places S.T.our.par D.st (S.msg m) _ hh.first fun i => ?_
  show S.msg m (S.T.wAt i) =
    (Gf.worldOf ρ mask entry).slot (posP (ldPartFmt K S.T.nv S.T.deg ++ [pDummy K S.T.DY]) hh.first i)
  rw [hw i, (coef_put S hs h i).world ρ mask entry, ρ.zero, ρ.sub, ρ.zero, ρ.one]
  ring

/-- A slot under which something lies is one of the ledger's. -/
theorem put_lt {G : Fork} {j : ℕ} {y f : E} (hz : Sized G) (h : Put G j y f) : j < G.ns := by
  rw [← hz.got]
  by_contra hc
  have := h.1
  simp [Array.getD, hc] at this

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.coef_put
#print axioms VerifiableInference.Desc.First.Att.P.D1_at
