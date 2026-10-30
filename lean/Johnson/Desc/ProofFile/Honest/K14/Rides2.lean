-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Rides2.lean: kind K14: «RIDESPAST» (Honest/Thread/Pays.lean) AT
THE MEMBERS 1 TO 8 OF THE SHARED CHAIN's THREAD, at this kind's letters (Honest/K14/Thread2.lean:
letters2). Statements with their proofs. NO PREMISE.

An item that is open in front of a member, and that the member's row neither shuts nor owes, says
behind, of ANY witness, what it says in front: from the thread in front and what the member's step
has left (keeps2). Which items these are is read off the table read forwards, by evaluation.

Main names:
  open1, shuts1, owes1, …, open8, shuts8, owes8   the table read forwards, at the eight members: by
                      evaluation
  ridesPast1          nothing goes past "LIN point"
  ridesPast2          at the sending of o_u: OmU, NearAt, RecAll: by the library's omU_of_same,
                      NearAt.of_same, RecAll.of_same, read forwards
  ridesPast3, ridesPast4, ridesPast6, ridesPast8   at "(rec_gamma)", "LOC", the joinings and
                      "SPLIT": by Johnson/Desc/K14/Honest/RidesQuiet.lean and SmpOwn.quiet. That o_u
                      stands, and how long the group's list is, come from the form in front (shapeK)
  ridesPast5          at the second sending, which brings messages: by smpOwn_send and rowsU_send
                      (RidesQuiet.lean). That the statement in front is in order comes from the
                      thread
  smpOwn_same, rowsU_same, ridesPast7   at "LIN zeta", which leaves the statement

What is not claimed. That the thread holds at any run. Nothing on the members 0 and 9 to 11: there
keeps is a letter of Others. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Thread2
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words InOrder)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc.Shared (ItemS)
open Desc.K14 (P14 St)
open Desc.K14.Honest
open Desc.K14.Law (QuietStep shapeK shapeU_iff shapeM_iff shapeO_iff RowsU rowsOn uRK omU_of_same
  NearAt RecAll)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice}

/-! ## The table read forwards, by evaluation -/

/-- What is open in front of the member number 1. -/
theorem open1 : fwdOpen SharedRows.start (SharedRows.rows true) 1 =
    ([.pinT] : List ItemS) := by
  decide

/-- What the member number 1 shuts. -/
theorem shuts1 : (SharedRows.rows true 1).shuts = ([.pinT] : List ItemS) := by
  decide

/-- What the member number 1 owes. -/
theorem owes1 : (SharedRows.rows true 1).owes = ([.omU, .nearU, .recRow] : List ItemS) := by
  decide

/-- What is open in front of the member number 2. -/
theorem open2 : fwdOpen SharedRows.start (SharedRows.rows true) 2 =
    ([.omU, .nearU, .recRow] : List ItemS) := by
  decide

/-- What the member number 2 shuts. -/
theorem shuts2 : (SharedRows.rows true 2).shuts = ([] : List ItemS) := by
  decide

/-- What the member number 2 owes. -/
theorem owes2 : (SharedRows.rows true 2).owes = ([.pin .oU, .row (.sample .oU)] : List ItemS) := by
  decide

/-- What is open in front of the member number 3. -/
theorem open3 : fwdOpen SharedRows.start (SharedRows.rows true) 3 =
    ([.omU, .nearU, .recRow, .pin .oU, .row (.sample .oU)] : List ItemS) := by
  decide

/-- What the member number 3 shuts. -/
theorem shuts3 : (SharedRows.rows true 3).shuts = ([.recRow] : List ItemS) := by
  decide

/-- What the member number 3 owes. -/
theorem owes3 : (SharedRows.rows true 3).owes = ([.row .recG, .pin .oU] : List ItemS) := by
  decide

/-- What is open in front of the member number 4. -/
theorem open4 : fwdOpen SharedRows.start (SharedRows.rows true) 4 =
    ([.omU, .nearU, .pin .oU, .row (.sample .oU), .row .recG] : List ItemS) := by
  decide

/-- What the member number 4 shuts. -/
theorem shuts4 : (SharedRows.rows true 4).shuts = ([.nearU] : List ItemS) := by
  decide

/-- What the member number 4 owes. -/
theorem owes4 : (SharedRows.rows true 4).owes = ([.row .loc, .pin .oU] : List ItemS) := by
  decide

/-- What is open in front of the member number 5. -/
theorem open5 : fwdOpen SharedRows.start (SharedRows.rows true) 5 =
    ([.omU, .pin .oU, .row (.sample .oU), .row .recG, .row .loc] : List ItemS) := by
  decide

/-- What the member number 5 shuts. -/
theorem shuts5 : (SharedRows.rows true 5).shuts = ([] : List ItemS) := by
  decide

/-- What the member number 5 owes. -/
theorem owes5 : (SharedRows.rows true 5).owes =
    ([.pin .oOmega, .row (.sample .oOmega), .pin .oSp, .row (.sample .oSp)] : List ItemS) := by
  decide

/-- What is open in front of the member number 6. -/
theorem open6 : fwdOpen SharedRows.start (SharedRows.rows true) 6 =
    ([.omU, .pin .oU, .row (.sample .oU), .row .recG, .row .loc, .pin .oOmega,
      .row (.sample .oOmega), .pin .oSp, .row (.sample .oSp)] : List ItemS) := by
  decide

/-- What the member number 6 shuts. -/
theorem shuts6 : (SharedRows.rows true 6).shuts = ([] : List ItemS) := by
  decide

/-- What the member number 6 owes. -/
theorem owes6 : (SharedRows.rows true 6).owes = ([] : List ItemS) := by
  decide

/-- What is open in front of the member number 7. -/
theorem open7 : fwdOpen SharedRows.start (SharedRows.rows true) 7 =
    ([.omU, .pin .oU, .row (.sample .oU), .row .recG, .row .loc, .pin .oOmega,
      .row (.sample .oOmega), .pin .oSp, .row (.sample .oSp)] : List ItemS) := by
  decide

/-- What the member number 7 shuts. -/
theorem shuts7 : (SharedRows.rows true 7).shuts = ([.omU] : List ItemS) := by
  decide

/-- What the member number 7 owes. -/
theorem owes7 : (SharedRows.rows true 7).owes =
    ([.row .fold, .pin .oU, .pin .oOmega] : List ItemS) := by
  decide

/-- What is open in front of the member number 8. -/
theorem open8 : fwdOpen SharedRows.start (SharedRows.rows true) 8 =
    ([.pin .oU, .row (.sample .oU), .row .recG, .row .loc, .pin .oOmega,
      .row (.sample .oOmega), .pin .oSp, .row (.sample .oSp), .row .fold] : List ItemS) := by
  decide

/-- What the member number 8 shuts. -/
theorem shuts8 : (SharedRows.rows true 8).shuts = ([.row .fold] : List ItemS) := by
  decide

/-- What the member number 8 owes. -/
theorem owes8 : (SharedRows.rows true 8).owes =
    ([.row .foldU, .row .foldOmega, .pin .oSp] : List ItemS) := by
  decide

/-! ## «RidesPast» -/

/-- **«RidesPast» at "LIN point"**: nothing goes past it: the one item that is open in front of it,
the committed table's pin, it shuts. -/
theorem ridesPast1 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 1 := by
  intro k s m E s' ps (i : ItemS) v _ _ hi hs _ _
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 1 := hi
  have hs' : i ∉ (SharedRows.rows true 1).shuts := hs
  rw [open1] at hi'
  rw [shuts1] at hs'
  exact absurd hi' hs'

/-- **«RidesPast» at the sending of o_u**: OmU, NearAt and RecAll go past it, at every witness. -/
theorem ridesPast2 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 2 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 2 s s' := (keepsAll_eq Q sentU O.keeps 2 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 2 := hi
  have hs' : i ∉ (SharedRows.rows true 2).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 2).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open2] at hi'
  rw [shuts2] at hs'
  rw [owes2] at ho'
  obtain ⟨e1, e2, e3, e4⟩ := hK.2.2.1 rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl
  · exact omU_of_same Q.par (uRK Q.par) O.lens.get
      (fun w y => O.lens.get w 2 .main ((linLayOmega Q.codes Q.par.S).index y)) s' s v e1.symm
      e3.symm h'
  · exact NearAt.of_same rdE e2.symm e3.symm h'
  · exact RecAll.of_same rdE e2.symm e3.symm e4.symm h'

/-- **«RidesPast» at "(rec_gamma)"**: OmU, NearAt and o_u's sample constraints go past it, at every
witness. -/
theorem ridesPast3 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 3 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 3 s s' := (keepsAll_eq Q sentU O.keeps 3 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 3 := hi
  have hs' : i ∉ (SharedRows.rows true 3).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 3).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open3] at hi'
  rw [shuts3] at hs'
  rw [owes3] at ho'
  have q : QuietStep s s' := hK.1 (by simp)
  have hf : (form2 Q O.shape 3 s && _) = true := hA.2.2.1.1
  rw [Bool.and_eq_true, form2_eq Q O.shape 3 s (by omega), Bool.and_eq_true] at hf
  have hk : shapeK Q.par 0 2 Q.par.S.fold.columns 3 s = true := hf.1.1
  obtain ⟨_, hse, _, _⟩ := (shapeU_iff Q.par _ _ s).1 ((shapeM_iff Q.par _ _ _ s).1 hk).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact omU_quiet Q.par (fun w y => w 2 .main ((linLayOmega Q.codes Q.par.S).index y)) q hse
      h'
  · exact nearAt_quiet Q.par q hse h'
  · exact absurd (by simp) hs'
  · exact absurd (by simp) ho'
  · exact SmpOwn.quiet q h'

/-- **«RidesPast» at "LOC"**: OmU, o_u's sample constraints and the constraints of "(rec_gamma)" go
past it, at every witness. -/
theorem ridesPast4 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 4 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 4 s s' := (keepsAll_eq Q sentU O.keeps 4 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 4 := hi
  have hs' : i ∉ (SharedRows.rows true 4).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 4).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open4] at hi'
  rw [shuts4] at hs'
  rw [owes4] at ho'
  have q : QuietStep s s' := hK.1 (by simp)
  have hf : (form2 Q O.shape 4 s && _) = true := hA.2.2.1.1
  rw [Bool.and_eq_true, form2_eq Q O.shape 4 s (by omega), Bool.and_eq_true] at hf
  have hk : shapeK Q.par 0 2 Q.par.S.fold.columns 4 s = true := hf.1.1
  obtain ⟨_, hse, _, hlen⟩ := (shapeU_iff Q.par _ _ s).1 ((shapeM_iff Q.par _ _ _ s).1 hk).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact omU_quiet Q.par (fun w y => w 2 .main ((linLayOmega Q.codes Q.par.S).index y)) q hse
      h'
  · exact absurd (by simp) hs'
  · exact absurd (by simp) ho'
  · exact SmpOwn.quiet q h'
  · exact rowsU_quiet q (by rw [hlen]; omega) h'

/-- **«RidesPast» at the sending of o_omega and o_sp**: OmU, o_u's pin and sample constraints and
the constraints of "(rec_gamma)" and "LOC" go past it, at every witness. That the statement in front
is in order comes from the thread. -/
theorem ridesPast5 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 5 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 5 s s' := (keepsAll_eq Q sentU O.keeps 5 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 5 := hi
  have hs' : i ∉ (SharedRows.rows true 5).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 5).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open5] at hi'
  rw [shuts5] at hs'
  rw [owes5] at ho'
  obtain ⟨e1, e3, g, q⟩ := hK.2.2.2.1 rfl
  have hI : InOrder s.st := hA.2.2.1.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · exact omU_of_same Q.par (uRK Q.par) O.lens.get
      (fun w y => O.lens.get w 2 .main ((linLayOmega Q.codes Q.par.S).index y)) s' s v e1.symm
      e3.symm h'
  · exact fun m' hm => smpOwn_send hI q (h' m' hm)
  · exact smpOwn_send hI q h'
  · exact rowsU_send hI q g h'
  · exact rowsU_send hI q g h'

/-- **«RidesPast» at the joinings**: all nine items that are open go past them, at every witness. -/
theorem ridesPast6 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 6 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 6 s s' := (keepsAll_eq Q sentU O.keeps 6 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 6 := hi
  have hs' : i ∉ (SharedRows.rows true 6).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 6).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open6] at hi'
  rw [shuts6] at hs'
  rw [owes6] at ho'
  have q : QuietStep s s' := hK.1 (by simp)
  have hf : (form2 Q O.shape 6 s && _) = true := hA.2.2.1.1
  rw [Bool.and_eq_true, form2_eq Q O.shape 6 s (by omega), Bool.and_eq_true] at hf
  have hk : shapeK Q.par 0 2 Q.par.S.fold.columns 6 s = true := hf.1.1
  obtain ⟨_, hse, _, hlen⟩ := (shapeU_iff Q.par _ _ s).1 ((shapeO_iff Q.par _ _ _ _ s).1 hk).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact omU_quiet Q.par (fun w y => w 2 .main ((linLayOmega Q.codes Q.par.S).index y)) q hse
      h'
  · exact fun m' hm => SmpOwn.quiet q (h' m' hm)
  · exact SmpOwn.quiet q h'
  · exact rowsU_quiet q (by rw [hlen]; omega) h'
  · exact rowsU_quiet q (by rw [hlen]) h'
  · exact fun m' hm => SmpOwn.quiet q (h' m' hm)
  · exact SmpOwn.quiet q h'
  · exact fun m' hm => SmpOwn.quiet q (h' m' hm)
  · exact SmpOwn.quiet q h'

/-- A message's sample constraints, where the statement stays. -/
theorem smpOwn_same {o : Nat} {a b : St} {m : Words Cb.Gl.E} (e : b.st = a.st)
    (h : SmpOwn o a m) : SmpOwn o b m := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, by rw [e]; exact hx, by rw [e]; exact hs⟩

/-- A stretch of the constraints on o_u's group, where the statement and the group's number stay. -/
theorem rowsU_same {i n : Nat} {a b : St} {m : Words Cb.Gl.E} (e : b.st = a.st)
    (g : b.loc.gU = a.loc.gU) (h : RowsU rdE i n a m) : RowsU rdE i n b m := by
  unfold RowsU rowsOn at h ⊢
  rw [e, g]
  exact h

/-- **«RidesPast» at "LIN zeta"**: the six items that it neither shuts nor owes go past it, at every
witness. -/
theorem ridesPast7 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 7 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 7 s s' := (keepsAll_eq Q sentU O.keeps 7 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 7 := hi
  have hs' : i ∉ (SharedRows.rows true 7).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 7).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open7] at hi'
  rw [shuts7] at hs'
  rw [owes7] at ho'
  obtain ⟨e, g⟩ := hK.2.1 rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by simp) hs'
  · exact absurd (by simp) ho'
  · exact smpOwn_same e h'
  · exact rowsU_same e g h'
  · exact rowsU_same e g h'
  · exact absurd (by simp) ho'
  · exact smpOwn_same e h'
  · exact fun m' hm => smpOwn_same e (h' m' hm)
  · exact smpOwn_same e h'

/-- **«RidesPast» at "SPLIT"**: the seven items that it neither shuts nor owes go past it, at every
witness. -/
theorem ridesPast8 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    RidesPast (letters2 Q sentU O Cl).thread 8 := by
  intro k s m E s' ps (i : ItemS) (v : Wt) hA hK₀ hi hs ho h
  have hK : keeps2 Q sentU 8 s s' := (keepsAll_eq Q sentU O.keeps 8 s s' (by omega)).mp hK₀
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 8 := hi
  have hs' : i ∉ (SharedRows.rows true 8).shuts := hs
  have ho' : i ∉ (SharedRows.rows true 8).owes := ho
  have h' : ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E) v := h
  show ItemS.holdsSh O.N (mgWords O.lens Q O.N (O.Mg₀ m.st.input)) i s'
      (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add ps)) v
  rw [open8] at hi'
  rw [shuts8] at hs'
  rw [owes8] at ho'
  have q : QuietStep s s' := hK.1 (by simp)
  have hf : (form2 Q O.shape 8 s && _) = true := hA.2.2.1.1
  rw [Bool.and_eq_true, form2_eq Q O.shape 8 s (by omega), Bool.and_eq_true] at hf
  have hk : shapeK Q.par 0 2 Q.par.S.fold.columns 8 s = true := hf.1.1
  obtain ⟨_, _, _, hlen⟩ := (shapeU_iff Q.par _ _ s).1 ((shapeO_iff Q.par _ _ _ _ s).1 hk).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun m' hm => SmpOwn.quiet q (h' m' hm)
  · exact SmpOwn.quiet q h'
  · exact rowsU_quiet q (by rw [hlen]; omega) h'
  · exact rowsU_quiet q (by rw [hlen]) h'
  · exact fun m' hm => SmpOwn.quiet q (h' m' hm)
  · exact SmpOwn.quiet q h'
  · exact absurd (by simp) ho'
  · exact SmpOwn.quiet q h'
  · exact absurd (by simp) hs'

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.open1
#print axioms ProofFile.Honest.K14.shuts1
#print axioms ProofFile.Honest.K14.owes1
#print axioms ProofFile.Honest.K14.open2
#print axioms ProofFile.Honest.K14.shuts2
#print axioms ProofFile.Honest.K14.owes2
#print axioms ProofFile.Honest.K14.open3
#print axioms ProofFile.Honest.K14.shuts3
#print axioms ProofFile.Honest.K14.owes3
#print axioms ProofFile.Honest.K14.open4
#print axioms ProofFile.Honest.K14.shuts4
#print axioms ProofFile.Honest.K14.owes4
#print axioms ProofFile.Honest.K14.open5
#print axioms ProofFile.Honest.K14.shuts5
#print axioms ProofFile.Honest.K14.owes5
#print axioms ProofFile.Honest.K14.open6
#print axioms ProofFile.Honest.K14.shuts6
#print axioms ProofFile.Honest.K14.owes6
#print axioms ProofFile.Honest.K14.open7
#print axioms ProofFile.Honest.K14.shuts7
#print axioms ProofFile.Honest.K14.owes7
#print axioms ProofFile.Honest.K14.open8
#print axioms ProofFile.Honest.K14.shuts8
#print axioms ProofFile.Honest.K14.owes8
#print axioms ProofFile.Honest.K14.ridesPast1
#print axioms ProofFile.Honest.K14.ridesPast2
#print axioms ProofFile.Honest.K14.ridesPast3
#print axioms ProofFile.Honest.K14.ridesPast4
#print axioms ProofFile.Honest.K14.ridesPast5
#print axioms ProofFile.Honest.K14.ridesPast6
#print axioms ProofFile.Honest.K14.smpOwn_same
#print axioms ProofFile.Honest.K14.rowsU_same
#print axioms ProofFile.Honest.K14.ridesPast7
#print axioms ProofFile.Honest.K14.ridesPast8
