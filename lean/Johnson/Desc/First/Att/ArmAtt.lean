-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/ArmAtt.lean: kind K5: THE ATTENTION SEGMENTS' HALF OF THE EXCHANGE ACROSS A
SEGMENT's SECOND SENDING: "the committed cell, read behind the sending, is the arm at the verifier's
state in front": ArmCellIn (Johnson/Desc/Sound/StatedCellIn.lean) at the
attention segments' arm uArm W (linkNo s) (Johnson/Desc/First/Att/K05StatedArm.lean). After the
pattern of the layers' armCell_lay (Johnson/Road/K4/ArmLay.lean).

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A RULE OVER LETTERS.

Main name:
  `armCellIn_att`: ArmCellIn Rd own own' piece run s a b rd (uArm W (linkNo s)).
EVERY PREMISE LEFT, AND WHOSE:
  hA: the public parameters have the attention plan of the open link's number: K5's files, with the
  promise's clause on the open link. hin: at s the claims' reading answers, at the plan's width: s
  lies behind K5's sub-protocol: K5's files. hNM: the tail's number of matrices is its list's size:
  public; shown at no plan yet; no idle premise (tile_needs_NM,
    Johnson/Desc/First/Att/Claims/TablesTile.lean).
  hW: the plan's width holds the tables: K5's files (plannedK_of_plan, K05PlannedK.lean).
  hE: NAMED, NOT PAID HERE: every form of the reader's answer has Cov: its entries lie in the
  tables' part of the array of the reads. The public
    test entInT does not give it (it bounds an entry by the layout's array's sizes). K5's files: the
    covering laws at the runs' and the readers' forms, with "the reader's list is just these forms".
    FROM hE ON THE ROAD IS PROVED: named_has_table, uAtt_at_named
    (Johnson/Desc/First/Att/K05NamedTable.lean).
  T: the smallness test's tie (TieOf, Johnson/Desc/First/K8/LawItems.lean) at the closed structure
  tl' behind the sending and a table of cells Ac:
    other files' to show.
  hfun: the closed structure's list of tables is what the arm reads in front: K5's files
  (block4_funs). htab: the plan's tail and the closed structure number the places alike: nobody's
  yet. hu3: the closed structure's number of the array of the reads is the plan's: nobody's yet.
  hAc: below nW, row 0 of the array of the reads in Ac is the data's cell behind the sending:
  cellsAt_name (CellsAtName.lean). hM: inside the ranges the matrices unpacked from the data
  in front are the tie's small integers: NOT PAID, here or at the layers. (The layers'
    form, InRange tl' M (cellA tl' A), is this sentence at aI := cellZ tl' Ac.) ITS TWO HALVES AND
    THEIR NAMED PAYERS: "the first sending's cells stay across the second sending": ExchangeStep
    and three companions that are not named [Johnson/Desc/K1/Law/ExchangeStep.lean is not imported;
    not called] · "small integers with Ac's packing are what the unpacking reads": cellZ_of_packs,
    cellA_syms (Johnson/Meaning/PlanesTieK8Cells.lean [not imported here; not called]).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05NamedTable
import Johnson.Desc.First.K8.LawItems
import Johnson.Desc.Sound.StatedCellIn
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ linkNo ArmCellIn)
open VerifiableInference.Desc.First.K8 (TieOf)
open OnBytes.Tie.Pv.Tail (tabAt_some)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open K5Law (funsAt Cov)

/-- **The attention segments' half of the exchange.** -/
theorem armCellIn_att {W : Verify.Public} {A : Attention.Plan} {s : First.S}
    {a b : VerifiableInference.Desc.K9.Part} {i : Runs.In} {tl' : HTailF2}
    {Ac : ℕ → ℕ → ℕ → Cb.Gl.E} (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (rd : ℕ × ℕ → MsgQ) (hA : W.A[linkNo s / 2]? = some A)
    (hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A))
    (hNM : A.seam.tl.NM = A.seam.tl.mats.size) (hW : A.nW ≤ plannedK A)
    (hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov A.iU3 (plannedK A) A.nW f)
    (T : TieOf tl' Ac) (hfun : tl'.funs.toList = funsAt A s)
    (htab : ∀ Fn c sg, A.seam.tl.tabAt Fn c sg = tl'.tabAt Fn c sg) (hu3 : u3Of tl' = A.iU3)
    (hAc : ∀ c, a.L.arrayOf[A.iU3]? = some c → ∀ i, i < A.nW →
      Ac A.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i)
    (hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)) :
    ArmCellIn Rd own own' piece run s a b rd (uArm W (linkNo s)) := by
  intro R hR f hf x hx _ c hc _
  have eu : uArm W (linkNo s) = uAtt A (funsAt A) := by
    unfold uArm
    rw [hA]
  rw [eu]
  have hy := hE R hR f hf x hx
  obtain ⟨Fn, hFn, c', sg, pos, e, hr, hi, hsum⟩ :=
    uAtt_at_named A hin hNM hy (dataQ own a rd) c
  obtain ⟨p, hp, ht, hr', hi'⟩ := hy
  have hpK : p < plannedK A := Nat.lt_of_lt_of_le hp hW
  have hpos : pos = p := by
    have a1 := Nat.div_add_mod pos (plannedK A)
    have a2 := Nat.div_add_mod p (plannedK A)
    rw [← hr, ← hi] at a1
    rw [← hr', ← hi'] at a2
    omega
  subst hpos
  have r0 : x.row = 0 := by rw [hr', Nat.div_eq_of_lt hpK]
  have i0 : x.idx = pos := by rw [hi', Nat.mod_eq_of_lt hpK]
  rw [hsum, r0, i0]
  rw [ht] at hc
  rw [← hAc c hc pos hp, ← hu3]
  obtain ⟨aI, h1, h2, h3⟩ := T
  have hmem : Fn ∈ tl'.funs.toList := by rw [hfun]; exact hFn
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hmem
  have hn' : tl'.funs[n]? = some Fn := by rw [← Array.getElem?_toList]; exact hn
  have e' : tl'.tabAt Fn c' sg = some pos := (htab Fn c' sg).symm.trans e
  rw [h3 n Fn hn' c' sg pos e']
  obtain ⟨g1, g2, g3, _⟩ := tabAt_some tl' e'
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < Fn.len := Finset.mem_range.mp hj
  have hlt : sg * Fn.len + j < (tl'.mats.getD Fn.mat {}).m := by
    have b1 : sg * Fn.len + j < (sg + 1) * Fn.len := by
      rw [Nat.succ_mul]
      omega
    have b2 : (sg + 1) * Fn.len ≤ (tl'.mats.getD Fn.mat {}).m / Fn.len * Fn.len :=
      Nat.mul_le_mul_right _ g3
    have b3 := Nat.div_mul_le_self (tl'.mats.getD Fn.mat {}).m Fn.len
    omega
  rw [hM aI h1 h2 Fn.mat (sg * Fn.len + j) c' g1 hlt g2]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.armCellIn_att
