-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/RowsAddr.lean: the code switch: WHAT THE TYPED TABLE AND THE TABLE OF
JOINTS' MEMBERS TAKE OF THE ROWS OF THE SENDINGS (Johnson.G.sendRowsOf), ENTRY BY ENTRY, BY ADDRESS:
general laws; no scope, no pin, no value.
  framesFrom_l · later_l  the frames of verify-on-bytes's planner bear their own numbers; the later
               ones, by place
  made_row     row m of tableFrom z sub R (Opts/TableFrom.lean) holds the
               rows' own entries: r.lo = linkList R m · r.l = link m + 1's first sending's sampled
               entries
  rows_labels · first_rows_labels  wherever sendRowsOf returns: the first chain's rows' LABELS and
               sampled shapes are the made sendings' own, in order (the laws
               rows_shapes | first_rows_shapes, Opts/RowsShapes.lean | RowsAtPlan.lean, with the
               label beside)
  entry · radOf_entry  the entry at an address (row k, place j); the radius that a member of the
               table bears (P5T.radOf) is that entry's, 0 where there is none: by definition
  addrsFrom · flat_addr · flat_addr_at  the entries of the rows whose label meets a test, one after
               the other, are the entries at a list of addresses that is made of the rows' labels
               and numbers of entries alone
  find_idx     the first row whose label meets a test, by its number among the labels
  ofLink · linkRows_first · linkList_at · linkHead_at  so: a link's list, and a link's first
               sending's list, entry by entry, by address
LIMITS. General laws on lists. No soundness is claimed.
-/
import Johnson.Top.H0.Opts.RowsAtPlan
import Johnson.Top.H0.Opts.TableFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Params OnBytes.Plan
open Johnson.G (Sending ChainSends SendRow sendsOf packListOf sendRowsOf linkRows linkList)
open Johnson.G.OfPlan (bind_ok)
open P1Opts (sampledOf pack_shapes zip_map_of ite_ok filter_key flat_filter)
open P5T (firstRows radOf rad?)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFrom)

/-! ## 1 The frames' numbers -/

theorem framesFrom_l (z : ProofSized) : ∀ (gs : List ReqGroup) (l : ℕ) (links : List ReqLink)
    (open_ : List ℕ) (before : GroupSize) (i : ℕ) (n : FrameN),
    (framesFrom z l gs links open_ before)[i]? = some n → n.l = l + i
  | [], _, _, _, _, _, _, h => by simp [framesFrom] at h
  | g :: gs, l, links, open_, before, i, n, h => by
    unfold framesFrom at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      rw [← h]
      rfl
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      cases hl : links.head? with
      | none => rw [hl] at h; simp at h
      | some x =>
        rw [hl] at h
        have := framesFrom_l z gs (l + 1) _ _ _ i n h
        omega

/-- The later frames, by place. -/
theorem later_l (z : ProofSized) (sub : Subproofs) (m : ℕ) (n : FrameN)
    (h : ((framesOf z sub).filter fun n => n.l != 0)[m]? = some n) : n.l = m + 1 := by
  unfold framesOf at h
  cases hf : framesFrom z 0 (reqGroups z.request).toList z.request.link sub.openRows
      z.link.group with
  | nil => rw [hf] at h; simp at h
  | cons a t =>
    have h0 : a.l = 0 := by
      have := framesFrom_l z _ 0 _ _ _ 0 a (by rw [hf]; rfl)
      omega
    have ht : ∀ x ∈ t, (x.l != 0) = true := by
      intro x hx
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      have := framesFrom_l z _ 0 _ _ _ (i + 1) x (by rw [hf, List.getElem?_cons_succ]; exact hi)
      rw [bne_iff_ne]
      omega
    rw [hf, List.filter_cons_of_neg (by rw [h0]; simp), List.filter_eq_self.2 ht] at h
    have := framesFrom_l z _ 0 _ _ _ (m + 1) n (by rw [hf, List.getElem?_cons_succ]; exact h)
    omega

/-- **The made table's row m holds the rows' own entries.** -/
theorem made_row (z : ProofSized) (sub : Subproofs) (R : List SendRow) (m : ℕ) (r : SwRow)
    (h : (tableFrom z sub R)[m]? = some r) :
    r.lo = linkList R m ∧ r.l = ((linkRows R (m + 1)).head?.map (·.sampled)).getD [] := by
  unfold tableFrom at h
  rw [List.getElem?_map] at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 h
  have e := later_l z sub m n hn
  refine ⟨?_, ?_⟩
  · show linkList R (n.l - 1) = linkList R m
    rw [e]
    rfl
  · show ((linkRows R n.l).head?.map (·.sampled)).getD [] = _
    rw [e]

/-! ## 2 The first chain's rows: labels beside shapes -/

/-- Wherever sendRowsOf returns, its rows' files, chains, labels and sampled shapes are the list of
sendings' own, row by row, in order. (Opts/RowsShapes.lean's rows_shapes, with the label beside.) -/
theorem rows_labels {pol lay KL : ByteArray} {rows : List SendRow} {sends : List ChainSends}
    (hr : sendRowsOf pol lay KL = .ok rows) (hs : sendsOf pol lay KL = .ok sends) :
    rows.map (fun r => ((r.file, r.chain), (r.label, r.sampled.map fun z => z.1))) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map
        fun cx => ((cx.1.file, cx.1.chain), (cx.2.label, sampledOf cx.2)) := by
  unfold sendRowsOf at hr
  rw [hs] at hr
  obtain ⟨sends', e, hr⟩ := bind_ok hr
  obtain rfl : sends = sends' := Except.ok.inj e
  obtain ⟨pack, hp, hr⟩ := bind_ok hr
  dsimp only at hr
  obtain ⟨t, hr⟩ := ite_ok hr
  have hlen := eq_of_beq t
  obtain rfl := Except.ok.inj hr
  have hflat : (sends.flatMap fun d => d.sends.map sampledOf) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map fun cx => sampledOf cx.2 := by
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
  have heq : pack.map (fun y => y.2.map fun z => z.1) =
      (sends.flatMap fun c => c.sends.map fun x => (c, x)).map fun cx => sampledOf cx.2 := by
    rw [← hflat]
    refine (pack_shapes hp hs).eq_of_length ?_
    rw [hflat, List.length_map, List.length_map, hlen]
  have hz := zip_map_of (fun cx : ChainSends × Sending => ((cx.1.file, cx.1.chain), cx.2.label))
    (fun y : Codes × List (OracleShape × ℕ) => y.2.map fun z => z.1)
    (fun cx => sampledOf cx.2) _ _ heq
  have hz2 := congrArg (List.map fun t : ((String × ℕ) × String) × List OracleShape =>
    (t.1.1, (t.1.2, t.2))) hz
  rw [List.map_map, List.map_map] at hz2
  rw [List.map_map]
  refine Eq.trans (List.map_congr_left ?_) hz2
  rintro ⟨⟨c, x⟩, p⟩ _
  rfl

/-- **The first chain's rows' labels and sampled shapes.** -/
theorem first_rows_labels {pol lay KL : ByteArray} {rows : List SendRow}
    {sends : List ChainSends} {p0 : ChainSends} (hr : sendRowsOf pol lay KL = .ok rows)
    (hs : sendsOf pol lay KL = .ok sends)
    (hP : sends.filter (fun c => c.file == "proof" && c.chain == 0) = [p0]) :
    (firstRows rows).map (fun r => (r.label, r.sampled.map fun z => z.1)) =
      p0.sends.map fun x => (x.label, sampledOf x) := by
  have h := filter_key (fun r : SendRow => (r.file, r.chain))
    (fun r => (r.label, r.sampled.map fun z => z.1))
    (fun cx : ChainSends × Sending => (cx.1.file, cx.1.chain))
    (fun cx => (cx.2.label, sampledOf cx.2))
    (fun q => q.1 == "proof" && q.2 == 0) _ _ (rows_labels hr hs)
  have e := flat_filter (fun c => c.file == "proof" && c.chain == 0) sends
  rw [hP] at e
  unfold firstRows
  refine h.trans ?_
  rw [e]
  simp [List.map_map, Function.comp_def]

/-! ## 3 Addresses -/

/-- The entry at an address (row k of the first chain's rows, place j among its sampled entries). -/
def entry (F : List SendRow) (a : ℕ × ℕ) : Option (OracleShape × ℕ) :=
  (F[a.1]?).bind (·.sampled[a.2]?)

/-- The radius that the table's members bear is the entry's. -/
theorem radOf_entry (R : List SendRow) (k j : ℕ) :
    radOf R k j = ((entry (firstRows R) (k, j)).map (·.2)).getD 0 := rfl

/-- The addresses of the entries of the rows whose label meets q, in order. W: each row's label and
number of sampled entries. n: the first row's number. -/
def addrsFrom (q : String → Bool) : ℕ → List (String × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | n, w :: W =>
    (if q w.1 then (List.range w.2).map fun j => (n, j) else []) ++ addrsFrom q (n + 1) W

theorem range_some {α : Type} (l : List α) :
    (List.range l.length).map (fun j => l[j]?) = l.map some := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem?_eq_getElem h1]

/-- **The picked rows' entries, one after the other, are the entries at the addresses.** -/
theorem flat_addr (q : String → Bool) : ∀ (suf pre : List SendRow),
    ((suf.filter fun r => q r.label).flatMap (·.sampled)).map some =
      (addrsFrom q pre.length (suf.map fun r => (r.label, r.sampled.length))).map
        (entry (pre ++ suf))
  | [], _ => rfl
  | r :: suf, pre => by
    have ih := flat_addr q suf (pre ++ [r])
    rw [List.append_assoc, List.length_append] at ih
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil,
      Nat.zero_add] at ih
    have hr : ∀ j, entry (pre ++ r :: suf) (pre.length, j) = r.sampled[j]? := by
      intro j
      unfold entry
      simp
    rw [List.map_cons]
    unfold addrsFrom
    rw [List.map_append, ← ih]
    by_cases hq : q r.label = true
    · have hq' : q (r.label, r.sampled.length).1 = true := hq
      rw [List.filter_cons, if_pos hq, List.flatMap_cons, List.map_append, if_pos hq',
        List.map_map]
      congr 1
      rw [← range_some]
      refine List.map_congr_left fun j _ => ?_
      exact (hr j).symm
    · have hq' : ¬ q (r.label, r.sampled.length).1 = true := hq
      rw [List.filter_cons, if_neg hq, if_neg hq']
      rfl

/-- The same, entry by entry. -/
theorem flat_addr_at (q : String → Bool) (F : List SendRow) (i : ℕ) :
    ((F.filter fun r => q r.label).flatMap (·.sampled))[i]? =
      ((addrsFrom q 0 (F.map fun r => (r.label, r.sampled.length)))[i]?).bind (entry F) := by
  have h := congrArg (fun l => l[i]?) (flat_addr q F [])
  simp only [List.getElem?_map, List.nil_append, List.length_nil] at h
  cases h1 : ((F.filter fun r => q r.label).flatMap (·.sampled))[i]? <;>
    cases h2 : (addrsFrom q 0 (F.map fun r => (r.label, r.sampled.length)))[i]? <;>
    simp [h1, h2] at h ⊢
  exact h

/-- The first row whose label meets q, by its number. -/
theorem find_idx (q : String → Bool) : ∀ F : List SendRow,
    F.find? (fun r => q r.label) = F[(F.map (·.label)).findIdx q]?
  | [] => rfl
  | r :: F => by
    cases hq : q r.label with
    | true => simp [List.findIdx_cons, hq]
    | false =>
      simp only [List.find?_cons, List.map_cons, List.findIdx_cons, hq, cond_false,
        List.getElem?_cons_succ]
      exact find_idx q F

/-- The label's test for «a sending of link l». -/
def ofLink (l : ℕ) (s : String) : Bool := s.startsWith s!"link {l},"

theorem linkRows_first (R : List SendRow) (l : ℕ) :
    linkRows R l = (firstRows R).filter fun r => ofLink l r.label := by
  unfold linkRows firstRows ofLink
  rw [List.filter_filter]
  refine List.filter_congr fun r _ => ?_
  rw [Bool.and_comm]

/-- **A link's list, entry by entry.** -/
theorem linkList_at (R : List SendRow) (l i : ℕ) :
    (linkList R l)[i]? = ((addrsFrom (ofLink l) 0
      ((firstRows R).map fun r => (r.label, r.sampled.length)))[i]?).bind
        (entry (firstRows R)) := by
  unfold linkList
  rw [linkRows_first]
  exact flat_addr_at (ofLink l) (firstRows R) i

/-- **A link's first sending's list, entry by entry.** -/
theorem linkHead_at (R : List SendRow) (l i : ℕ) :
    (((linkRows R l).head?.map (·.sampled)).getD [])[i]? =
      entry (firstRows R) (((firstRows R).map (·.label)).findIdx (ofLink l), i) := by
  rw [linkRows_first, List.head?_filter, find_idx]
  unfold entry
  cases (firstRows R)[((firstRows R).map (·.label)).findIdx (ofLink l)]? <;> rfl

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.radOf_entry
#print axioms VerifiableInference.Desc.First.K2Ties.range_some
#print axioms VerifiableInference.Desc.First.K2Ties.flat_addr
#print axioms VerifiableInference.Desc.First.K2Ties.flat_addr_at
#print axioms VerifiableInference.Desc.First.K2Ties.find_idx
#print axioms VerifiableInference.Desc.First.K2Ties.linkRows_first
#print axioms VerifiableInference.Desc.First.K2Ties.linkList_at
#print axioms VerifiableInference.Desc.First.K2Ties.linkHead_at

#print axioms VerifiableInference.Desc.First.K2Ties.rows_labels
#print axioms VerifiableInference.Desc.First.K2Ties.first_rows_labels

#print axioms VerifiableInference.Desc.First.K2Ties.framesFrom_l
#print axioms VerifiableInference.Desc.First.K2Ties.later_l
#print axioms VerifiableInference.Desc.First.K2Ties.made_row
