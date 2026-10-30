-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawTie.lean: THE SMALLNESS TEST: "THE SENT READS ARE THE TRUE ONES" AS ONE
PLAIN FORMULA OVER THE CARRIED RECORD'S OWN READERS, AND THAT WHAT STANDS IN FRONT OF THE DRAW GIVES
IT.

The table of joints of the first chain has a letter `tie`: each entry of the vector of reads that a
table names is the stated function of the cells behind the committed symbols. In the proved block
that sentence is a part of its first joint (`relIn`), typed over sizes. Here it is said with no
typed size, in the words of the record of the smallness test that lies in the carried record, of a
table of cells A (array, row, column):
  `TieOf tl A`: there is an integer for each (matrix, row of cells, column) such that (1) each is
    below twice the shift in absolute value; (2) their packing, column by column, is the symbols:
    the cells of A at the matrix's symbol array; (3) FOR EVERY TABLE Fn OF tl's CLOSED LIST and all
    c, sg, pos with tl.tabAt Fn c sg = some pos: the cell (the reads' array, 0, pos) of A is the sum
    over j below Fn.len of the reading of Fn.phi[j] times the integer at (Fn.mat, sg * Fn.len + j,
    c).
  `TieAt A s w`: a link is open, and `TieOf` holds at its record and at A w.
  `tieK8 A`: the same in the type of the table's letter (segment, record, strings, witness).
  `tie_of_relIn`: the proved block's first joint at the letters of
    Johnson/Desc/First/K8/LawLay.lean gives `TieOf`.
  `tie_of_relA`: **what stands in front of the kind's block gives the tie**, at the witness's own
    committed entries.
Definitions, statements and proofs. The formula follows the library's `reads_at`
(OnBytes/Tie/Pv/Tail/LettersAt.lean), which says it at the library's letters.
Limits. (3) SPEAKS OF THE ENTRIES THAT THE CLOSED LIST'S TABLES NAME, AND OF NO OTHER: an entry of
the vector of reads that a kind's form reads and no table names is free. Whether the tables name all
entries that the kinds' forms read is each kind's to say. The integers stand under "there is": that
they are the only ones is `cellsOK_cellsOf`'s (Johnson/Desc/First/K8/LawReads.lean), under the
no-wrap premise. The segment's number is not read: the formula speaks of the link that is open. One
way alone. The letters and premises of LawLay.lean stand.
`TieOf`, `TieAt` and `tieK8` are defined in Johnson/Desc/First/K8/LawItems.lean.

-/
import Johnson.Desc.First.K8.LawLay
import Johnson.Desc.First.K8.LawItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)

/-- The packing of a column reads its number of rows alone. -/
theorem pack_congr {m m' : ℕ} (h : m = m') (r : ℤ) (f : ℕ → ℤ) (i' : ℕ) :
    Alg.pack r (fun i : Fin m => f i) i' = Alg.pack r (fun i : Fin m' => f i) i' := by
  subst h
  rfl

/-- The proved block's first joint, at the letters of LawLay.lean, gives the tie. -/
theorem tie_of_relIn
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (tl : HTailF2) (hp : SamePub tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (w : Wit Cells Tok MsgT)
    (h : relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE)
      (u3L Y tl0 entE) (digL Y tl0 entW)).letters (blank tl) (msgsOf cs l seat' arr w)) :
    TieOf tl fun a r c => Y.cellAt (entW w) a r c := by
  obtain ⟨b, h1, h2, h3⟩ := reads_of_relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT)
    (symL Y tl0 entE) (u3L Y tl0 entE) (digL Y tl0 entW)) h
  have hU : u3Of tl = u3Of tl0 := by
    unfold u3Of
    rw [hp.ix]
  refine ⟨fun μ i c => b μ c i, ?_, ?_, ?_⟩
  · intro μ hμ c hc i hi
    rw [hp.nm] at hμ
    rw [hp.k] at hc
    rw [hp.m] at hi
    exact h1 μ hμ c hc i hi
  · intro μ hμ c hc i' hi'
    rw [hp.nm] at hμ
    rw [hp.k] at hc
    rw [hp.m] at hi'
    rw [hp.gt, pack_congr (hp.m μ)]
    refine Eq.trans ?_ (h2 μ hμ c hc i' hi')
    refine (cellAt_congr Y _ _ _ _ _ fun j hj => hE w j ?_).symm
    rw [hj]
    exact early_sym (Nat.lt_of_lt_of_le hμ hgt) i' c
  · intro n Fn hn c sg pos hpos
    obtain ⟨g1, g2, g3, rfl⟩ := tabAt_some tl hpos
    have hT : (OnBytes.Tie.Pv.Tail.sizeOf tl0).tabs[n]? = some ⟨Fn.mat, Fn.len, Fn.start⟩ := by
      have ht := hp.tabs
      unfold SameShapes at ht
      show (tl0.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))[n]? = _
      rw [← ht, List.getElem?_map, Array.getElem?_toList, hn]
      rfl
    have hφ : ∀ j, phiAt Reading.gl (blank tl) n j = Reading.gl.val (Fn.phi.getD j zeroE) := by
      intro j
      unfold phiAt
      have e : (blank tl).funs.getD n default = Fn := by
        show tl.funs.getD n default = Fn
        rw [Array.getD_eq_getD_getElem?, hn]
        rfl
      rw [e]
    rw [hp.nm] at g1
    rw [hp.k] at g2
    rw [hp.m] at g3
    have h4 := h3 n ⟨Fn.mat, Fn.len, Fn.start⟩ hT g1 c g2 sg g3
    rw [hU, hp.m]
    refine Eq.trans ?_ (h4.trans (Finset.sum_congr rfl fun j _ => ?_))
    · refine (cellAt_congr Y _ _ _ _ _ fun j hj => hE w j ?_).symm
      rw [hj]
      exact early_u3 hu _ _
    · show phiAt Reading.gl (blank tl) n j * _ = _
      rw [hφ j]

variable {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- **What stands in front of the kind's block gives the tie**, at the witness's own committed
entries: where a link is open and the condition's second half holds. -/
theorem tie_of_relA
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (recOf tl0 a.1) tl0) (hz : SameSize tl tl0)
    (h : (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA a w) :
    TieAt (fun w a r c => Y.cellAt (entW w) a r c) a.1 w := by
  have hx : recOf tl0 a.1 = blank tl := by
    unfold recOf
    rw [ht]
    rfl
  have hp : SamePub tl tl0 := by
    rw [hx] at hp0
    exact { toSameSize := hz, toSameLay := ⟨hp0.gt, hp0.ix, hp0.mz, hp0.off⟩ }
  have h' : relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE)
      (u3L Y tl0 entE) (digL Y tl0 entW)).letters (recOf tl0 a.1) (msgsOf cs l seat' arr w) :=
    h.2.2
  rw [hx] at h'
  exact ⟨tl, ht, tie_of_relIn Y tl0 cs l seat' arr entE entW hE tl hp hgt hu w h'⟩

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.tie_of_relIn
#print axioms VerifiableInference.Desc.First.K8.tie_of_relA
