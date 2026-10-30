-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortSeam.lean: the claim before the lookup on the digits of a smallness
test, at the verifier's own record; and a test on the shape that ties the numbering to the fields
which the verifier's claim on the keys reads.

Main names:
  `PortOK tl`, `portTest`, `portOK_of_test`: what the verifier's own claims read of the record,
    tied: each piece passes the verifier's own `HTailF2.pieceHeld` (so off is a multiple of 2^b, 2^a
    = Rp, b = a + clog2 CP), lies in ZZ and begins at column q mz; the forest's calls have the n, k,
    t0 of the two calls that `transcriptF` hands to `Forest.pad`; both tables are range tables, and
    row t holds t; t0 = 0 at both calls; 2^cK = NC; the widths are t2D0 and t2D1.
  `shapeTest2`: `shapeTest` (PortLaws.lean) and `portTest`.
  `dgP_t0`: the padding row is row 0 at both calls.
  `dgP_sh_port`: (portQJ tl en).sh St = Port.Q tl.f9 (fun _ => Tp) (fun _ nu => KpJ tl en nu).
  `dgP_in_iff`: "for every call c < NC: InTable n_c k_c (KpJ tl en nu c) (T c)" holds if and only if
    every low digit lies in [0, 2^t2D0) and every high digit in [0, 2^t2D1); for every T that holds
    t in row t < 2^k_c.
  `dgP_cell`, `mapJ_ok_iff`.
Limits: that `shapeTest2` follows from the success of the verifier's own routines is not shown. It
is a Bool on public numbers that runs at full size. That it is true at a given sub-proof is a run,
no proof term: whoever uses these statements at a sub-proof takes it as a named hypothesis, or
decides it in the kernel (untried). That the verifier's claim on the joint keys binds these keys,
that is, that the coefficients which the verifier computes are those of `KFl` (PortKeys.lean), is
not shown: it is held by a run at one small made-up shape alone. Nothing on the claims behind the
lookup.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Blocks

/-- What the port's own claims read of the tail, tied. -/
structure PortOK (tl : HTailF2) : Prop where
  held : ∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q,
    HTailF2.pieceHeld (tl.zOf q).call.n p = true ∧ p.tree = tl.ix.ZZ ∧ p.c0 = q * tl.mz
  call : ∀ q < tl.f9.NC, Port.nOf tl.f9 q = (tl.zOf q).call.n ∧ Port.kOf tl.f9 q = (tl.zOf q).call.k
      ∧
    Port.t0Of tl.f9 q = (tl.zOf q).call.t0 ∧ (tl.zOf q).call.tau.isNone = true ∧
    (tl.f9.calls.getD q {}).tau.isNone = true ∧ Port.t0Of tl.f9 q = 0
  full : 2 ^ tl.f9.cK = tl.f9.NC
  wide : Port.kOf tl.f9 0 = t2D0 ∧ Port.kOf tl.f9 1 = t2D1
  rows : ∀ q < tl.f9.NC, ∀ t < 2 ^ Port.kOf tl.f9 q, ((tl.f9.calls.getD q {}).tauAt t).toNat = t

def portTest (tl : HTailF2) : Bool :=
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q,
    HTailF2.pieceHeld (tl.zOf q).call.n p = true ∧ p.tree = tl.ix.ZZ ∧ p.c0 = q * tl.mz) &&
  decide (∀ q < tl.f9.NC, Port.nOf tl.f9 q = (tl.zOf q).call.n ∧ Port.kOf tl.f9 q = (tl.zOf
      q).call.k ∧
    Port.t0Of tl.f9 q = (tl.zOf q).call.t0 ∧ (tl.zOf q).call.tau.isNone = true ∧
    (tl.f9.calls.getD q {}).tau.isNone = true ∧ Port.t0Of tl.f9 q = 0) &&
  decide (2 ^ tl.f9.cK = tl.f9.NC) && decide (Port.kOf tl.f9 0 = t2D0 ∧ Port.kOf tl.f9 1 = t2D1) &&
  decide (∀ q < tl.f9.NC, ∀ t < 2 ^ Port.kOf tl.f9 q, ((tl.f9.calls.getD q {}).tauAt t).toNat = t)

theorem portOK_of_test {tl : HTailF2} (h : portTest tl = true) : PortOK tl := by
  simp only [portTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The whole test on the shape. -/
def shapeTest2 (tl : HTailF2) (pp : ℕ) : Bool := shapeTest tl pp && portTest tl

variable {tl : HTailF2} {J : Type} (en : Ent3 → J)

theorem shape2_parts {pp : ℕ} (h : shapeTest2 tl pp = true) : shapeTest tl pp = true ∧ TailOK tl ∧
    PortOK tl := by
  simp only [shapeTest2, Bool.and_eq_true] at h
  have h1 := h.1
  simp only [shapeTest, Bool.and_eq_true] at h1
  exact ⟨h.1, tailOK_of_test h1.1.1, portOK_of_test h.2⟩

/-- t0 = 0 at both calls. -/
theorem dgP_t0 (hP : PortOK tl) : ∀ q < tl.f9.NC, Port.t0Of tl.f9 q = 0 := fun q hq => (hP.call q
    hq).2.2.2.2.2

theorem dgP_t00 (hT : TailOK tl) (hP : PortOK tl) : Port.t0Of tl.f9 0 = 0 :=
  dgP_t0 hP 0 (by rw [hT.nc]; decide)

/-- `DatOK` of the one if and only if of the other. -/
theorem mapJ_ok_iff {I J J' : Type} (Q : DatQ I J) (en : J → J') {q H pp : ℕ} :
    (Q.mapJ en).DatOK q H pp ↔ Q.DatOK q H pp :=
  ⟨fun h =>
    { posLt := h.posLt, inv := h.inv, inv' := h.inv', callK := h.callK, kLt := h.kLt,
      tLt := h.tLt, rowLo := h.rowLo, rowHi := h.rowHi, ofLo := h.ofLo, ofHi := h.ofHi,
      zero := h.zero, tagLt := h.tagLt, tagInj := h.tagInj, pads := h.pads, laid := h.laid },
    mapJ_ok Q en⟩

section
variable {E : Type} [Field E]

/-- The data of the digits' shift are `Port.Q` at the verifier's record, as one equation. -/
theorem dgP_sh_port (hT : TailOK tl) (hP : PortOK tl) (St : Type) :
    (portQJ tl en).sh (E := E) St = Port.Q tl.f9 (fun _ => Tp) (fun _ ν => KpJ tl en ν) := by
  have hk : (fun (_ : St) (μ : J → E) => (portQJ tl en).key μ) =
      fun _ ν => Port.key tl.f9 (Tp (E := E)) (KpJ tl en ν) := by
    funext _ ν X
    exact dgP_key_portJ en hT (dgP_t00 hT hP) ν X
  unfold DatQ.sh Port.Q
  rw [hk]
  rfl

omit [Field E] in
/-- `InTable` reads the table below 2^k alone. -/
theorem inTable_congr {n k : ℕ} {key T T' : ℕ → E} (h : ∀ t < 2 ^ k, T t = T' t) :
    InTable n k key T ↔ InTable n k key T' :=
  ⟨fun g b hb => by obtain ⟨u, hu, e⟩ := g b hb; exact ⟨u, hu, by rw [e, h u hu]⟩,
   fun g b hb => by obtain ⟨u, hu, e⟩ := g b hb; exact ⟨u, hu, by rw [e, h u hu]⟩⟩

/-- The claim before the lookup, at the verifier's record: the digits lie in their tables. -/
theorem dgP_in_iff {pp : ℕ} (h : shapeTest2 tl pp = true) (ν : J → E) (T : ℕ → ℕ → E)
    (hTab : ∀ c < tl.f9.NC, ∀ t < 2 ^ Port.kOf tl.f9 c, T c t = ((t : ℕ) : E)) :
    (∀ c < tl.f9.NC, InTable (Port.nOf tl.f9 c) (Port.kOf tl.f9 c) (KpJ tl en ν c) (T c)) ↔
      (∀ i : Pl tl, Cb.Rng.InTab (2 ^ t2D0) (ν (en (tl.ix.ZZ, i.2.val, i.1.val)))) ∧
      ∀ i : Pl tl, Cb.Rng.InTab (2 ^ t2D1) (ν (en (tl.ix.ZZ, i.2.val, tl.mz + i.1.val))) := by
  obtain ⟨h1, hT, hP⟩ := shape2_parts h
  have e1 : (∀ c < tl.f9.NC, InTable (Port.nOf tl.f9 c) (Port.kOf tl.f9 c) (KpJ tl en ν c) (T c)) ↔
      ∀ c < tl.f9.NC, InTable (Port.nOf tl.f9 c) (Port.kOf tl.f9 c) (KpJ tl en ν c) (Tp (E := E) c)
          :=
    forall₂_congr fun c hc => inTable_congr (hTab c hc)
  rw [e1, ← Cb.port_in_iff E tl.f9 Tp (KpJ tl en ν) hT.port]
  have hk : Port.key tl.f9 (Tp (E := E)) (KpJ tl en ν) = (portQJ tl en).key ν := by
    funext X
    exact (dgP_key_portJ en hT (dgP_t00 hT hP) ν X).symm
  rw [hk]
  exact dgQ_in (portQJ tl en) (dgP_port_okJ en h1) ν

/-- The place of a bit, with a test on the call's number before it, is the place of the record of
the
digits: the test never fails, since 2^cK = NC. -/
theorem dgP_cell (hP : PortOK tl) (u j : ℕ) :
    (if u % 2 ^ tl.f9.cK < tl.f9.NC then some (bcJ tl en (u / 2 ^ tl.f9.cK) (u % 2 ^ tl.f9.cK) j)
        else none) =
      some ((portQJ tl en).bAt u j) := by
  have hlt : u % 2 ^ tl.f9.cK < tl.f9.NC := by
    rw [← hP.full]
    exact Nat.mod_lt _ (by positivity)
  rw [if_pos hlt, dgP_bcJ]

end

#print axioms portOK_of_test
#print axioms dgP_t0
#print axioms mapJ_ok_iff
#print axioms dgP_sh_port
#print axioms dgP_in_iff
#print axioms dgP_cell

end OnBytes.DgP
