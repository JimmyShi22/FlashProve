-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontEndTrees.lean: W's tree at the end of the first chain's
fold, under the head AtMgA at the older hash.

  lay_written      the closed lay of W's message: both in one new tree
  behind_parts, sendAtS_parts   the new tree holds the two messages
  wTree_at_end     W's tree at the end: number 82, its shape, the parts 197 and 198, at no list opened

Limits.
- The full size alone.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEndMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (sendAtS)
open VerifiableInference.Desc.K13.Law (linAt LFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- W's message at the written parameters. -/
def msgW : Array OracleNotice := (linMessageW proofSizedFull.batch.shape).getD #[]

set_option maxRecDepth 1000000 in
theorem lay_written : ((layTrees Johnson.G.codesFull2 msgW).getD {}).tree.getD 0 0 = 0 ∧
    ((layTrees Johnson.G.codesFull2 msgW).getD {}).tree.getD 1 0 = 0 ∧
    ((layTrees Johnson.G.codesFull2 msgW).getD {}).shapes.toList.length = 1 := by
  decide +kernel

/-- **The new tree holds the two messages**, where both sit in the one new tree. -/
theorem behind_parts {L : Type} (P : VerifiableInference.Desc.K1.Par) (d : _root_.Desc.Plain.DState L)
    (seeds : List (List E × E)) (ys : List E) (h2 : P.sent.size = 2)
    (t0 : ((layTrees P.codes P.sent).getD {}).tree.getD 0 0 = 0)
    (t1 : ((layTrees P.codes P.sent).getD {}).tree.getD 1 0 = 0)
    (hs : ((layTrees P.codes P.sent).getD {}).shapes.toList.length = 1) (T : OnBytes.Tree)
    (hT : (VerifiableInference.Desc.K1.behind P d seeds ys).book.trees[d.book.trees.size]? = some T) :
    T.parts = #[d.st.oracles.size, d.st.oracles.size + 1] := by
  have e : (VerifiableInference.Desc.K1.behind P d seeds ys).book.trees =
      partsLaid P.sent ((layTrees P.codes P.sent).getD {}) d.st.oracles.size d.book.trees.size
        (treesSent P.gp.firstTree ((layTrees P.codes P.sent).getD {}).shapes.toList d.roots
          d.book.trees) := rfl
  rw [e] at hT
  obtain ⟨x, hx⟩ : ∃ x, ((layTrees P.codes P.sent).getD {}).shapes.toList = [x] :=
    List.length_eq_one_iff.1 hs
  rw [hx] at hT
  unfold partsLaid at hT
  rw [h2] at hT
  have er : List.range 2 = [0, 1] := rfl
  rw [er] at hT
  simp only [List.foldl_cons, List.foldl_nil, t0, t1, Nat.add_zero] at hT
  rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_modify, if_pos rfl] at hT
  have e₂ : treesSent P.gp.firstTree [x] d.roots d.book.trees =
      d.book.trees.push { shape := x, number := P.gp.firstTree + d.roots, src := .own d.roots } := rfl
  rw [e₂, Array.getElem?_push_eq] at hT
  simp only [Option.map_some, Option.some.injEq] at hT
  rw [← hT]
  rfl

theorem sendAtS_parts {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') (h2 : P.sent.size = 2)
    (t0 : ((layTrees P.codes P.sent).getD {}).tree.getD 0 0 = 0)
    (t1 : ((layTrees P.codes P.sent).getD {}).tree.getD 1 0 = 0)
    (hs : ((layTrees P.codes P.sent).getD {}).shapes.toList.length = 1) (T : OnBytes.Tree)
    (hT : s'.book.trees[s.book.trees.size]? = some T) :
    T.parts = #[s.st.oracles.size, s.st.oracles.size + 1] := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (VerifiableInference.Desc.K1.map_ok _ _ _).1 hy
      obtain ⟨_, _, e⟩ := (VerifiableInference.Desc.K1.decideSend_iff P _ _ x.2 r₁ r₂ x.1).1 hx
      have hT' : x.2.book.trees[s.book.trees.size]? = some T := hT
      rw [e] at hT'
      exact behind_parts P _ _ _ h2 t0 t1 hs T hT'
    · cases h
  · cases h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A tree's shape by the written list. -/
theorem tree_shape {L : VerifiableInference.Desc.K12.Door.Laid} {B : TreeBook}
    (h : VerifiableInference.Desc.K12.Door.seatsCarriedB L B = true) {z : ℕ} {T : OnBytes.Tree}
    (hT : B.trees[z]? = some T) : L.shapes[z]? = some T.shape := by
  unfold VerifiableInference.Desc.K12.Door.seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.trees.toList.map (·.shape) = L.shapes.take B.trees.size := eq_of_beq h.1.2
  have hz := (Array.getElem?_eq_some_iff.1 hT).1
  have e₁ : (B.trees.toList.map (·.shape))[z]? = some T.shape := by
    rw [List.getElem?_map, Array.getElem?_toList, hT]
    rfl
  rw [e, List.getElem?_take_of_lt hz] at e₁
  exact e₁

/-- **W's tree at the end of the first chain's fold.** -/
theorem wTree_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) {l : LinFirst} (hl : linAt e₁ = some l) :
    e₁.book.trees.size = 83 ∧
    ∃ T : OnBytes.Tree, e₁.book.trees[82]? = some T ∧ T.number = 82 ∧ T.shape = wTree.shape ∧
      T.parts = #[197, 198] ∧ T.lists = 0 := by
  have EW := endWritten h hf hm
  obtain ⟨hw, -, -, -⟩ := atW_numbers h hf hm hl
  have hstep : e₁.st.oracles.size = e₁.book.place.size := by rw [EW.msgs, EW.places]
  obtain ⟨q, T, hq, hT, hlist⟩ := newTrees_at_end h hf hm hstep hl 197 (by omega) (by rw [EW.msgs]; omega)
  have hq' := EW.place 197 (by omega)
  rw [hq, places_written.2.1] at hq'
  obtain rfl := Option.some.inj hq'
  have hnum := EW.number _ _ hT
  have hsh := tree_shape EW.seats hT
  rw [treeShapes_written.2] at hsh
  suffices hs : e₁.book.trees.size = 83 ∧ T.parts = #[197, 198] from
    ⟨hs.1, T, hT, hnum, (Option.some.inj hsh).symm, hs.2, hlist⟩
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
  have hr : ∃ a b, R₁ = [a, b] := by
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  have h' := h.toAtMg
  have Wr := H2K12.written354_of_pins h'.scope h'.laid.pub h'.pins.1
    (h'.laid.run ▸ LPFD.Full.laidPOf_of h'.laid.value h'.laid.planOk h'.laid.data h'.laid.asks)
  have hsize := msg_written h hmsg
  have hmW : msg = msgW := by
    unfold msgW
    rw [← lin_at_head h, hmsg]
    rfl
  have hsent : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent = msg := by
    simp [VerifiableInference.Desc.K1.Par.sent, VerifiableInference.Desc.K1.parW]
  have hcodes : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).codes = Johnson.G.codesFull2 :=
    Wr.codes
  have B := VerifiableInference.Desc.K1.sendAtS_booked _ t mid a b G₁ h1
  obtain ⟨m₁, l₁, o', owed, hs₀, -, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have est : e₁.st = o'.2.st := by rw [es]
  have ebook : e₁.book = mid.book := by rw [es]
  have hcnt : e₁.st.oracles.size = mid.st.oracles.size := by
    rw [est]
    exact (VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows).count
  have hmsgs := B.msgs
  rw [hsent, hsize] at hmsgs
  have h199 := EW.msgs
  have ht : t.st.oracles.size = 197 := by omega
  have hplace : mid.book.place.size = t.book.place.size + 2 := by
    rw [B.place]
    simp [hsent, hsize]
  have hn : t.book.place.size = t.st.oracles.size := by
    have h₃ := EW.places
    rw [ebook, hplace] at h₃
    omega
  have hpl := B.newer hn (i := 0) (by rw [hsent, hsize]; omega)
  have hl₁ := lay_written
  rw [← hcodes, ← hmW, ← hsent] at hl₁
  rw [← ebook, ht] at hpl
  have hq₂ := EW.place 197 (by omega)
  rw [places_written.2.1] at hq₂
  rw [show (197 + 0 : ℕ) = 197 from rfl, hq₂] at hpl
  have e₈₂ : 82 = t.book.trees.size := by
    have k := congrArg Prod.fst (Option.some.inj hpl)
    have k₀ : (VerifiableInference.Desc.K1.layOf (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)).tree.getD 0 0 = 0 := hl₁.1
    dsimp only at k
    rw [k₀] at k
    exact k
  have hT₂ : mid.book.trees[t.book.trees.size]? = some T := by
    rw [← e₈₂, ← ebook]
    exact hT
  have hp := sendAtS_parts _ t mid a b G₁ h1 (by rw [hsent]; exact hsize) hl₁.1 hl₁.2.1 hl₁.2.2 T hT₂
  rw [ht] at hp
  refine ⟨?_, hp⟩
  have hs₁ : (VerifiableInference.Desc.K1.layOf (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)).shapes.size = 1 := by
    have k : (VerifiableInference.Desc.K1.layOf (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)).shapes.toList.length = 1 :=
      hl₁.2.2
    simpa using k
  rw [ebook, B.trees, hs₁, ← e₈₂]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.behind_parts
#print axioms ProofFile.Honest.K12.AtFile.wTree_at_end
