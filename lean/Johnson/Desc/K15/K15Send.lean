-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Send.lean: beneath K15's law: what a yes of the sending (sendP
over its plain ground) says at the link's one
message, with one answer to a sample: the facts that the library's record LinkSent
(OnBytes/Slice/BlkLinkRan.lean) holds of a run of
`verify-on-bytes`'s sending, here of the plain text: no program is run.
-/
import Johnson.Desc.K15.GroundInv
import OnBytes.Slice.BlkLinkRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

variable {L : Type}

/-- Items that are all answers to a sample are these answers' words. -/
theorem answersOf_inv : ∀ (vals : List Fmt.ItemValue) (dr : Fmt.Drawn) (ys : List E),
    answersOf ⟨vals, dr⟩ = some ys → vals = ys.map fun y => Fmt.ItemValue.answer y.triple
  | [], _, ys, h => by
    simp [answersOf] at h
    subst h
    rfl
  | g :: l, dr, ys, h => by
    cases hl : answersOf ⟨l, dr⟩ with
    | none =>
      unfold answersOf at h hl
      cases g <;> simp_all [List.mapM_cons]
    | some zs =>
      have ih := answersOf_inv l dr zs hl
      unfold answersOf at h hl
      cases g <;> simp_all [List.mapM_cons]
      subst h
      simp [E.triple_ofTriple]

/-- The book after the link's message, from a carried record. -/
def bookAfter (ft : Nat) (d : DState L) (sent : Array OracleNotice) (lay : TreeLay) : TreeBook :=
  { trees := partsLaid sent lay d.st.oracles.size d.book.trees.size
      (treesSent ft lay.shapes.toList d.roots d.book.trees)
    place := d.book.place ++ (Array.range sent.size).map fun i =>
      (d.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }

/-- What the sending's yes says. -/
structure SentP (S : LinkShape) (ft : Nat) (d d' : DState L) (ids : Array Nat) (lay : TreeLay)
    (beta y0 y1 : E) (row0 row1 : Row) (places : List PadPlace) (r2 r3 : Fmt.RoundView) : Prop where
  laid : layTrees d.st.codes (linkMessage S 1) = some lay
  numbers : ids = (Array.range (linkMessage S 1).size).map (· + d.st.oracles.size)
  vals2 : r2.vals = []
  factor : (r2.drawn.elems.map E.ofTriple).drop (Send.cube d.st.codes (rowShape S)).bits = [beta]
  nz : isZeroE beta = false
  vals3 : r3.vals = [.answer y0.triple, .answer y1.triple]
  form0 : Send.form d.st.codes (rowShape S) d.st.oracles.size
    ⟨(r2.drawn.elems.map E.ofTriple).take (Send.cube d.st.codes (rowShape S)).bits, beta⟩ 0 = some
        row0
  form1 : Send.form d.st.codes (rowShape S) (d.st.oracles.size + 1)
    ⟨(r2.drawn.elems.map E.ofTriple).take (Send.cube d.st.codes (rowShape S)).bits, beta⟩ 0 = some
        row1
  pad : Send.pad d.st.codes (rowShape S) = some places
  out : d' = { d with
    st := admitted (admitted (stSent d.st (linkMessage S 1)) d.st.oracles.size (rowShape S)
      places #[{ row0 with target := y0 }]) (d.st.oracles.size + 1) (rowShape S) places
      #[{ row1 with target := y1 }]
    book := bookAfter ft d (linkMessage S 1) lay
    roots := d.roots + lay.shapes.size }
  placed : d.st.oracles.size = d.book.place.size

theorem sendLink_inv (S : LinkShape) (p : GPar) (d d' : DState L) (r2 r3 : Fmt.RoundView) (ids : Array Nat)
    (sd an : List E) (need : Nat)
    (h : sendP groundG p true d (linkMessage S 1) r2 r3 = some (ids, sd, an, need, d')) :
    ∃ lay beta y0 y1 row0 row1 places,
      SentP S p.firstTree d d' ids lay beta y0 y1 row0 row1 places r2 r3 := by
  unfold sendP at h
  simp only [VerifiableInference.Desc.Own.seedsMade_eq, ←
      VerifiableInference.Desc.Own.allZero_agrees] at h
  cases hr : groundG.recv p d (linkMessage S 1) with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨ids₁, d₁⟩ := x
    obtain ⟨lay, hlay, hpl, hids, hd₁⟩ := recvP_inv p.firstTree d d₁ _ ids₁ hr
    have hst : d₁.st = stSent d.st (linkMessage S 1) := by rw [hd₁]
    obtain ⟨q0, q1, -⟩ := linkSent_oracles S d.st
    have htodo : (ids₁.toList.filter fun o =>
        ((d₁.st.oracles[o]?).map (·.shape.answers)).getD 0 != 0) =
        [d.st.oracles.size, d.st.oracles.size + 1] := by
      rw [hst, hids]
      exact linkSent_todo S d.st
    rw [hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, htodo, List.mapM_cons, List.mapM_nil] at h
    rw [hst] at h
    simp only [q0, q1, Option.map_some, Option.bind_some, Option.pure_def] at h
    have hans : (rowShape S).answers = 1 := rfl
    have hcodes : (stSent d.st (linkMessage S 1)).codes = d.st.codes := rfl
    simp only [List.foldl_cons, List.foldl_nil, hans, Nat.zero_max, Nat.max_self, hcodes,
        Nat.zero_add,
      Nat.reduceAdd] at h
    cases hs : Send.seedsOf (Send.cube d.st.codes (rowShape S)).bits 1
        (List.map E.ofTriple r2.drawn.elems) with
    | none => simp [hs] at h
    | some seeds =>
      obtain ⟨beta, hbeta, rfl⟩ := seedsOf_one _ _ _ hs
      rw [hs] at h
      simp only [Option.bind_some] at h
      cases ha : answersOf { vals := List.take 2 r3.vals, drawn := r3.drawn } with
      | none => simp [ha] at h
      | some an₁ =>
        rw [ha] at h
        simp only [Option.bind_some] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_eq_true, false_or,
            beq_iff_eq, List.isEmpty_iff, List.all_cons, List.all_nil, Bool.and_true,
            Bool.not_eq_true'] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨_, hv2⟩, _⟩, _⟩, _⟩, hnz⟩, hlen⟩, hv3, _⟩ := hc
          match an₁, hlen with
          | [y0, y1], _ =>
            simp only [List.zip_cons_cons, List.zip_nil_right, sampleLoop, hans, List.range_succ,
              List.range_zero, List.nil_append, rowsFor, List.getElem?_cons_zero,
              VerifiableInference.Desc.Own.formMade_eq] at h
            cases hf0 : Send.form d.st.codes (rowShape S) d.st.oracles.size
                ⟨List.take (Send.cube d.st.codes (rowShape S)).bits
                    (List.map E.ofTriple r2.drawn.elems),
                  beta⟩ 0 with
            | none => simp [hf0] at h
            | some row0 =>
              rw [hf0] at h
              simp only at h
              cases ha0 : groundG.admit p d₁ d.st.oracles.size (#[].push { row0 with target := y0 })
                  with
              | none => rw [ha0] at h; simp at h
              | some d₂ =>
                rw [ha0] at h
                simp only [rowsFor, List.getElem?_cons_zero,
                    VerifiableInference.Desc.Own.formMade_eq] at h
                cases hf1 : Send.form d.st.codes (rowShape S) (d.st.oracles.size + 1)
                    ⟨List.take (Send.cube d.st.codes (rowShape S)).bits
                      (List.map E.ofTriple r2.drawn.elems), beta⟩ 0 with
                | none => simp [hf1] at h
                | some row1 =>
                  rw [hf1] at h
                  simp only at h
                  cases ha1 : groundG.admit p d₂ (d.st.oracles.size + 1)
                      (#[].push { row1 with target := y1 }) with
                  | none => rw [ha1] at h; simp at h
                  | some d₃ =>
                    rw [ha1] at h
                    simp only [Option.bind_some, List.isEmpty_nil, if_true] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, _, _, _, rfl⟩ := h
                    obtain ⟨x0, places, a1, a2, rfl⟩ := admitP_inv d₁ d₂ _ _ ha0
                    rw [hst] at a1 a2
                    obtain rfl := Option.some.inj (q0.symm.trans a1)
                    obtain ⟨x1, places', b1, b2, rfl⟩ := admitP_inv _ d₃ _ _ ha1
                    simp only [hst] at b1 b2
                    rw [admitted_other _ _ _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_self _))] at b1
                    obtain rfl := Option.some.inj (q1.symm.trans b1)
                    obtain rfl : places = places' := Option.some.inj (a2.symm.trans b2)
                    have hv := answersOf_inv _ _ _ ha
                    rw [List.take_of_length_le (Nat.le_of_eq hv3)] at hv
                    refine ⟨lay, beta, y0, y1, row0, row1, places, hlay, hids, hv2, hbeta, hnz, hv,
                        hf0, hf1,
                      a2, ?_, hpl⟩
                    rw [hd₁]
                    rfl
        · cases h

end Desc.K15
