-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawLay.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LETTERS WITH THE SYMBOLS,
THE VECTOR OF READS AND THE DIGITS READ OFF ONE TABLE OF CELLS.

Johnson/Desc/First/K8/LawAtRecord.lean leaves three letters free: `sym` (which entry of which
member's message is a symbol of a matrix), `u3` (which is an entry of the vector of reads), `dig`
(the digits off the witness). The library reads all three off ONE table of cells (array, row,
column), at the arrays and columns that the verifier's record names (`AtA`,
OnBytes/Tie/Pv/Tail/EndsAt.lean; with the sizes as a letter: `AtT`, EndsCut.lean), and takes the
cells from a lay Y of the committed entries (`Lay`, OnBytes/Tie/Pv/Led/LedJoint.lean): `Y.cellAt m`,
which is 0 outside the lay's addresses. Here the three letters are DEFINED so, at the public record
tl0. What stays free is how the committed entries are read: `entE`, off the messages of the
signature; `entW`, off the file's one witness; and ONE LAW that ties them (`hE`): on an entry whose
address is a cell of an array that is fixed before the draw (`early`,
OnBytes/Tie/Pv/Tail/LettersAt.lean) the two agree.
  `SameSize tl tl0`: the record tl has the public record's NUMBERS (matrices, their rows and
    columns, combinations, shapes of tables). `sizeOf_same`: so it has its sizes. `SameLay tl tl0`:
    it has its LAYOUT (the symbol arrays' numbers, the arrays' index, the digits' columns).
    `SamePub`: both.
  `symL`, `u3L`, `digL`: the three readings. `layReads`: the member of the letters; ITS CONDITION IS
    `SameLay` at the record in the state (`lay_onA`), because the three readings take their arrays
    and columns from tl0. THE NUMBERS ARE NO PART OF THE CONDITION: a yes of the kind's block gives
    them (Johnson/Desc/First/K8/LawPlace.lean).
  `lay_keepsW`: the kind's law in the plain form there.
  `lay_atT`: **THE LIBRARY'S PREMISE ON LETTERS IS PAID**: `AtT` holds at these letters, at every
    record tl with `SamePub` that holds the list of β and the running sums as first columns, at the
    witness's messages and digits, at the cells `Y.cellAt (entW w)`.
  `relOut_cut`: the library's `relOut_of_rows` with the sizes as a letter.
  `lay_relB_of_rows`: so what stands behind the kind's block holds, if the pins hold, the digits
    are in their tables and every single equation of the list is 0 at these cells.
Definitions, statements and proofs.
Limits. STILL LETTERS: J, Y (the lay) · entE, entW (THAT ENTRY (row, column) OF ARRAY a IS PLACE q
OF ROW r OF THE MESSAGE THAT HOLDS a is said nowhere here: it is owed, with `hE`) · smpOf · l,
seat', arr. STILL PREMISES of `lay_relB_of_rows`: the condition's second half (`SameLay` at the
record in the state) · `SameSize` · each matrix has its symbol array, and the vector of reads its
array, in tl0's lists · the shapes fit (`Fits`) · every table lies on the third vector of reads
· the pins · the digits in their tables · every single equation. One way alone. Nothing says that
what stands at a boundary holds.

-/
import Johnson.Desc.First.K8.LawAtPlan
import OnBytes.Tie.Pv.Tail.EndsAtPort
import OnBytes.Tie.Pv.Tail.HostLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

/-- The record tl has the public record's NUMBERS: as many matrices, each with its rows and columns;
the number of combinations; the shapes of the tables. -/
structure SameSize (tl tl0 : HTailF2) : Prop where
  nm : tl.NM = tl0.NM
  m : ∀ μ, (tl.mats.getD μ {}).m = (tl0.mats.getD μ {}).m
  k : ∀ μ, (tl.mats.getD μ {}).k = (tl0.mats.getD μ {}).k
  tau : tl.tau = tl0.tau
  tabs : SameShapes tl0 tl.funs

/-- The record tl has the public record's LAYOUT: the symbol arrays' numbers, the arrays' index, the
digits' columns. -/
structure SameLay (tl tl0 : HTailF2) : Prop where
  gt : tl.gtTree = tl0.gtTree
  ix : tl.ix = tl0.ix
  mz : tl.mz = tl0.mz
  off : tl.off = tl0.off

/-- Both. -/
structure SamePub (tl tl0 : HTailF2) : Prop extends SameSize tl tl0, SameLay tl tl0

theorem sizeOf_same {tl tl0 : HTailF2} (h : SameSize tl tl0) :
    OnBytes.Tie.Pv.Tail.sizeOf tl = OnBytes.Tie.Pv.Tail.sizeOf tl0 := by
  have ht := h.tabs
  unfold SameShapes at ht
  unfold OnBytes.Tie.Pv.Tail.sizeOf
  simp only [h.nm, h.m, h.k, h.tau, ht]

/-- The digits' columns are the public record's. -/
theorem zzCol_same {tl tl0 : HTailF2} (h : SamePub tl tl0) (μ q i : ℕ) :
    tl.zzCol μ q i = tl0.zzCol μ q i := by
  simp only [HTailF2.zzCol, h.nm, h.m, h.mz, h.off]

/-- The library's `relOut_of_rows`, with the sizes as a letter. -/
theorem relOut_cut {K : Type} [Field K] {ρ : OnBytes.Model.Reading K} (tl : HTailF2) {t : TSize}
    (ht : OnBytes.Tie.Pv.Tail.sizeOf tl = t) {Θ : TLetters K t} {x : Θ.X} {msg : Θ.M}
    {Z : Dig K t.size} {β : Dr t.size} {A : Nat → Nat → Nat → K} (pc : Nat)
    (at' : AtT ρ tl t Θ x msg Z β A) (hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ u i, Cb.Rng.InTab t.size.lo (Z.zl μ u i) ∧ Cb.Rng.InTab t.size.hi (Z.zh μ u i))
    (hrows : ∀ r ∈ rowsTail ρ tl tl.funs pc, r.2 A = 0) : relOut Θ.letters x β msg Z := by
  subst ht
  exact relOut_of_rows pc ⟨at'.phi, at'.sym, at'.u3, at'.zl, at'.zh, at'.th⟩ hfit htree hdig hrows

section
variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2)

/-- The symbol (matrix, row of symbols, column): a cell of the matrix's symbol array. -/
def symL {M : Type} (ent : M → J → Cb.Gl.E) (m : M) (μ i' c : ℕ) : Cb.Gl.E :=
  Y.cellAt (ent m) (tl0.gtTree.getD μ 0) i' c

/-- An entry of the vector of reads: a cell of the one row of its array. -/
def u3L {M : Type} (ent : M → J → Cb.Gl.E) (m : M) (pos : ℕ) : Cb.Gl.E :=
  Y.cellAt (ent m) (u3Of tl0) 0 pos

/-- The digits: cells of the digits' array, at the verifier's columns. -/
def digL {W : Type} (ent : W → J → Cb.Gl.E) (w : W) :
    Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0).size :=
  ⟨fun μ u i => Y.cellAt (ent w) tl0.ix.ZZ u ((tl0.zzCol μ 0 0).getD 0 + i),
    fun μ u i => Y.cellAt (ent w) tl0.ix.ZZ u ((tl0.zzCol μ 1 0).getD 0 + i)⟩

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ)
  (arr : ℕ → ℕ → ℕ) {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)

/-- **The library's premise on letters is paid.** -/
theorem lay_atT
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (tl : HTailF2) (hp : SamePub tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) (hβ : tl.cfF = listOf β)
    (w : Wit Cells Tok MsgT) :
    AtT Reading.gl tl (OnBytes.Tie.Pv.Tail.sizeOf tl0)
      (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE) (u3L Y tl0 entE)
        (digL Y tl0 entW))
      (blank tl) (msgsOf cs l seat' arr w) (digL Y tl0 entW w) β
      (fun a r c => Y.cellAt (entW w) a r c) where
  phi := fun n Fn hn j _ => by
    show phiAt Reading.gl (blank tl) n j = _
    unfold phiAt
    have e : (blank tl).funs.getD n default = Fn := by
      show tl.funs.getD n default = Fn
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn]
      rfl
    rw [e]
  sym := fun μ i' c hμ _ _ => by
    show Y.cellAt (entE _) (tl0.gtTree.getD μ 0) i' c = Y.cellAt (entW w) (tl.gtTree.getD μ 0) i' c
    rw [hp.gt]
    refine cellAt_congr Y _ _ _ _ _ fun j hj => hE w j ?_
    rw [hj]
    exact early_sym (Nat.lt_of_lt_of_le (hp.nm ▸ hμ) hgt) i' c
  u3 := fun y _ d _ => by
    show Y.cellAt (entE _) (u3Of tl0) 0 _ = Y.cellAt (entW w) (u3Of tl) 0 _
    have e : u3Of tl = u3Of tl0 := by
      unfold u3Of
      rw [hp.ix]
    rw [e]
    refine cellAt_congr Y _ _ _ _ _ fun j hj => hE w j ?_
    rw [hj]
    exact early_u3 hu _ _
  zl := fun μ u i => by
    show Y.cellAt (entW w) tl0.ix.ZZ u ((tl0.zzCol μ 0 0).getD 0 + i) =
      Y.cellAt (entW w) tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)
    rw [hp.ix, zzCol_same hp]
  zh := fun μ u i => by
    show Y.cellAt (entW w) tl0.ix.ZZ u ((tl0.zzCol μ 1 0).getD 0 + i) =
      Y.cellAt (entW w) tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i)
    rw [hp.ix, zzCol_same hp]
  th := fun μ u c => by
    have h := th_draw (K := Cb.Gl.E) tl (sizeOf_same hp.toSameSize) hnm hfirst β μ u c
    rw [← hβ] at h
    exact h

variable {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- The member of the letters: symbols, reads and digits off one table of cells; the condition: the
record in the state has the public record's numbers, arrays, columns and shapes of tables. -/
def layReads : Reads Cl (Wit Cells Tok MsgT) F atS p base e
    (callerAtRecord tl0
      (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE) (u3L Y tl0 entE)
        (digL Y tl0 entW))
      (sigOf cs l) id (fun x => SameLay x.1 tl0)) :=
  frameReads G cs l seat' arr tl0
    (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE) (u3L Y tl0 entE)
      (digL Y tl0 entW))
    id (fun x => SameLay x.1 tl0) (recOf tl0) () smpOf id (recOf_put tl0) hs Cl F p base e hseat

/-- The condition in front: no collision at the record's samples on the words that the frame's own
strings show; and the record in the state has the public record's layout. -/
theorem lay_onA (a : S × F.E.Str) :
    (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onA a ↔
      (sigOf cs l).CF (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) ∧
        SameLay (recOf tl0 a.1) tl0 :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩

/-- **The kind's law in the plain form, there.** -/
theorem lay_keepsW (hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onA
      (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).onB
      (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA
      (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relB
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err :=
  hear_keepsW _ hf (OnBytes.Tie.Pv.Tail.sizeOf_ok tl0) he

/-- **From the single equations back to what stands behind the kind's block, at these letters.** -/
theorem lay_relB_of_rows
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (recOf tl0 a.1) tl0) (hz : SameSize tl tl0) (hgt : tl0.NM ≤ tl0.gtTree.size)
    (hu : ∃ t, tl0.ix.U[2]? = some (some t)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) (hβ : tl.cfF = listOf β)
    (hdec : ∀ i, (sigOf cs l).decs (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) i =
      some (msgsOf cs l seat' arr w i))
    (pc : Nat) (hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ u i,
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.lo ((digL Y tl0 entW w).zl μ u i) ∧
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.hi ((digL Y tl0 entW w).zh μ u i))
    (hrows : ∀ r ∈ rowsTail Reading.gl tl tl.funs pc,
      r.2 (fun a r c => Y.cellAt (entW w) a r c) = 0) :
    (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relB a w := by
  have hx : recOf tl0 a.1 = blank tl := by
    unfold recOf
    rw [ht]
    rfl
  have hp : SamePub tl tl0 := by
    rw [hx] at hp0
    exact { toSameSize := hz, toSameLay := ⟨hp0.gt, hp0.ix, hp0.mz, hp0.off⟩ }
  have hcf : (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).cf a.1 =
      listOf β := by
    show (a.1.tl?.map (·.cfF)).getD #[] = _
    rw [ht]
    exact hβ
  have ho := relOut_cut tl (sizeOf_same hz) pc
    (lay_atT Y tl0 cs l seat' arr entE entW hE tl hp hgt hu hnm hfirst β hβ w) hfit htree hdig hrows
  rw [← hx] at ho
  exact Reads.relB_of_relOut _ a w β hcf hdec trivial ho

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.lay_atT
#print axioms VerifiableInference.Desc.First.K8.relOut_cut
#print axioms VerifiableInference.Desc.First.K8.lay_relB_of_rows
#print axioms VerifiableInference.Desc.First.K8.lay_onA
#print axioms VerifiableInference.Desc.First.K8.lay_keepsW
