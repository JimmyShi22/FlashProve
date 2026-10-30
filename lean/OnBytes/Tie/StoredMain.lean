-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredMain.lean: an accepted chain that opens stored tables, and the compiled verifier
of the library's theory.

An entry file's chain opens two stored tables, whose roots are outside the chain. The library
turns the description of such a chain and a decision into a protocol that reads the two tables as
two strings (Run/PlanQX.lean). It types what a reader has read as a proof string of that protocol
(`Run.PQ.toBPrfX`), and it has the compiled verifier of the protocol in a form that can be evaluated
(`Run.PQ.VX`). This file proves: if the strict reader has read the chain and the decision says yes,
then the typing gives a string, and that verifier accepts this string. The compiled verifier is
`Compile.Batch.verifyOneProtocol` at the tag "link": the verifier of one slot, with the strict format, that
the library's compiled scheme calls.

It holds for every decision, for a chain that begins at any byte of a file, under any record of tree
vertices, with random bytes in the file or given, and for the fast forms that the program runs.

The hypotheses. The description is within the limits (`withinX`), and the sizes are within bounds
(`smallFX`, OnBytes/Tie/StoredDom.lean). Both tests can be evaluated. The roots r0 and r1 have 32
bytes. `stm r0 r1` is the chain's statement. The statement's item of each table that the chain opens
holds that table's root: item 0 holds r0, item 1 holds r1. The last two bind a caller less than they
seem to. A constant `stm` will do, and then the typed first query does not read the roots;
OnBytes/Tie/EntryFile.lean takes the function that builds the statement. And the root of a table
that the chain does not open is free.

Which chains. Of the chains that the program reads, the entry file's is the one that the limits fit.
That it is within them is a theorem at two sets of parameter bytes (OnBytes/Tie/EntryGrounds.lean,
ZeroRecordLines.lean); in the theorems on the program's check `withinX` stays a
hypothesis. The shared chain of a key or of a proof opens one stored table too. But where one of its
rounds sends two roots (docs/format/FORMAT.md, R13.19), it is outside the limits. The test key's
shared chain is outside them (OnBytes/Tie/TestNotCovered.lean).

Main definitions: `xdOf`, `ownOut`, `withinX`, `CompiledAcceptsX`.
Main theorems: `stored_core`, `stored_VX`, `stored_compiled`, `readInX_compiled`.

Which protocol. Like that of OnBytes/Tie/OneChain.lean, and it reads the two tables as two strings.
To accept it asks, besides, that every part of the draws has its full number and that every symbol
of a stored table carries its place. The verifier's key is the two roots; the parameters' digest is
built into the typed first query.

What is not claimed. Nothing on soundness. The library's `lu_sound` on this protocol's interface is
for the relation that holds of everything, with a decoder that accepts every string: true and empty
(OnBytes/Tie/OneChain.lean). Unlike that file's protocol, this one reads two strings, so a theorem
on soundness for a language of these strings could have content. It would need an encoding and a
decoder that belong to a code, and soundness round by round for that language. Neither is stated for
this protocol in this directory or in the library (head of Run/PlanQXDoor.lean); that road is the
matter of OnBytes/Slice/. What OneChain.lean lists
as not claimed is not claimed here either. That the two roots are the right ones is the caller's
matter: the key file is not checked here. That a description meets `withinX` is a theorem for two
entries alone (OnBytes/Tie/EntryGrounds.lean, ZeroRecordLines.lean); for any other it is a
test to be evaluated.
-/
import OnBytes.Tie.StoredTop
import OnBytes.Tie.Session

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- A description with stored tables in the library's form. `stm` gives the statement's bytes as a
function of the two tables' roots. The chain's random bytes count as standing in the file. -/
def xdOf (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) : XD :=
  ⟨inFile S.base, stm, S.stored⟩

/-- A chain as read, without the stored tables' openings and without the vertices met. -/
def ownOut (pd R rho0 rho : ByteArray)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))) : Fmt.ChainOut :=
  ⟨pd, some R, rho0, rho, [], (rc.map fun p => stripR p.1).toArray⟩

/-- A member of the second list has a partner in a first list no shorter. -/
theorem exists_zip_left {α β : Type} : ∀ (l1 : List α) (l2 : List β) (x : β), x ∈ l2 →
    l2.length ≤ l1.length → ∃ c, (c, x) ∈ l1.zip l2
  | _, [], _, h, _ => by cases h
  | [], _ :: _, _, _, h => by simp at h
  | a :: l1, b :: l2, x, h, hl => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨a, by simp⟩
    · obtain ⟨c, hc⟩ := exists_zip_left l1 l2 x h' (by simpa using hl)
      exact ⟨c, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hc⟩

/-- If R relates two lists and P holds on the first, "R and P" relates them. -/
theorem forall2_and_left {α β : Type} {R : α → β → Prop} {P : α → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → (∀ x ∈ l1, P x) →
      List.Forall₂ (fun x y => R x y ∧ P x) l1 l2
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hp =>
    .cons ⟨h, hp _ List.mem_cons_self⟩
      (forall2_and_left t fun x hx => hp x (List.mem_cons_of_mem _ hx))

section
variable (S : Fmt.SpecX) (hS : S.ok = true)

include hS in
/-- In a description in order every round's stored tables meet the format's conditions. -/
theorem specX_round : ∀ x ∈ S.base.rounds.zip S.stored,
    Fmt.storedOk S.base.statement x.1 x.2 = true := by
  unfold Fmt.SpecX.ok at hS
  simp only [Bool.and_eq_true, List.all_eq_true] at hS
  exact hS.2

include hS in
/-- The parts of a round's draws end within the round's number of draws. -/
theorem specX_parts : ∀ x ∈ S.base.rounds.zip S.stored, ∀ t ∈ x.2,
    t.lo + t.count ≤ x.1.entry.poss := by
  intro x hx t ht
  have h := specX_round S hS x hx
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [List.isEmpty_iff.1 h] at ht
    cases ht
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact partsFrom_le x.2 0 _ h.1.2 t ht

include hS in
/-- A stored table's tree is a stored tree with the number 0. -/
theorem specX_shape : ∀ t ∈ S.stored.flatten, t.sh.stored = true ∧ t.sh.tree = 0 := by
  intro t ht
  obtain ⟨ts, hts, htt⟩ := List.mem_flatten.1 ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at htt
    cases htt
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    have := h.2 t htt
    exact ⟨this.1.1.1.1.1.1.1.1, this.1.1.1.2⟩

end

section
variable (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- `StoredFact` of each table's opening in rc gives `StoOK` of o's stored openings, if o is rc with
these joined in, S is in order, hD holds (one depth, the plan's salts), each table is opened at most
once and the items hold the roots. -/
theorem stoOK_of (r0 r1 : ByteArray) (hS : S.ok = true) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hF : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc)
    (hD : ∀ s ∈ S.stored.flatten, s.sh.a = (xdOf S stm).a ∧ s.salt = S.base.plan.salt)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0)) :
    StoOK O S.base.cfg (xdOf S stm).a S.base.plan.salt r0 r1 (storedB (xdOf S stm).xs o) := by
  have hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
      S.stored rc := hF.imp fun _ _ hh => hh.length_eq
  have key : ∀ e ∈ storedB (xdOf S stm).xs o, ∃ (t : Fmt.Stored)
      (z : Fmt.Shape × List ℕ × Fmt.OpenOut) (poss : List ℕ), t ∈ S.stored.flatten ∧
      StoredFact (Fmt.HO O) S.base.cfg S.base.statement poss t z ∧
      e = (t.item == 1, z.1.W, obOf z) := by
    intro e he
    rw [xs_eq, show (xdOf S stm).stored = S.stored from rfl, storedB_eq S.stored o rc ho hl] at he
    obtain ⟨tp, htp, he'⟩ := List.mem_flatMap.1 he
    obtain ⟨tz, htz, rfl⟩ := List.mem_map.1 he'
    have h1 := (List.forall₂_iff_zip.1 hF).2 (show (tp.1, tp.2) ∈ _ from htp)
    have h2 := (List.forall₂_iff_zip.1 h1).2 (show (tz.1, tz.2) ∈ _ from htz)
    exact ⟨tz.1, tz.2, _, List.mem_flatten.2 ⟨tp.1, (List.of_mem_zip htp).1,
      (List.of_mem_zip htz).1⟩, h2, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sto_keys (Fmt.HO O) (xdOf S stm) o rc ho hF]
    exact honce
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    have := F.okb
    rw [(hD t ht).2] at this
    show (⟨z.1.a, z.2.1, z.2.2.cols, z.2.2.salts, z.2.2.given⟩ : OpenB).ok S.base.plan.salt z.1.W
      = true
    rw [F.sh]
    exact this
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    show z.1.a = _
    rw [F.sh]
    exact (hD t ht).1
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    exact (WalkTie.listOK_spec _ _ F.okl).1
  · intro e he
    obtain ⟨t, z, poss, ht, F, rfl⟩ := key e he
    have hw := F.walk
    have hr := (F.root.symm.trans (hroot t ht))
    obtain ⟨hs1, hs2⟩ := specX_shape S hS t ht
    have hsh : t.sh = ⟨(xdOf S stm).a, z.1.W, true, 0⟩ := by
      rw [F.sh, ← (hD t ht).1, ← hs1, ← hs2]
    rw [hsh] at hw
    exact hw.trans (Option.some.inj hr)

include hO in
/-- If the strict reader, at the hash that O induces, has read a chain that opens stored tables and
the decision is yes, the typing gives a typed string and the evaluable form of the compiled verifier
accepts it. O is any function on byte strings with answers of 32 bytes whose digest of the
parameters is the format's (`hpd`). The other hypotheses are those of `stored_VX` without `smallFX`,
with the clauses of `withinX` one by one. -/
theorem stored_core (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf S stm).ok = true) (hn : S.base.rand.isNone = false)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : Fmt.HO O 169 0 1 Fmt.zero32 S.base.params = Fmt.paramsDigest S.base.params)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) :
    ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧
      verifyP (fun _ => (xdOf S stm).L dec) (famX (xdOf S stm) dec O ((xdOf S stm).K + 1)) id none
        (256 + 8 * S.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        (wqX (xdOf S stm).C (xdOf S stm).K (chalP S.base.plan.field (xdOf S stm).K)
          (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec
          (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  have hok' := hok
  unfold XD.ok at hok'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
  obtain ⟨⟨hokb, -⟩, hall⟩ := hok'
  have hbok : (inFile S.base).ok = true := base_ok _ hokb
  obtain ⟨hSok, x, i0, hd, s, hr, hst', hf, rfl, rfl⟩ := readX_stages (Fmt.HO O) S seen b i o j e
  obtain ⟨rnd, rfl⟩ := rnd_some S.base b i x i0 hn hr
  obtain ⟨hdrun, rho0⟩ := hd
  obtain ⟨h32, hrun, hrho⟩ := startChain_some (Fmt.HO O) _ _ _ _ _ hst'
  obtain ⟨R, hR⟩ : ∃ R : ByteArray, hdrun = some R := ⟨_, hrun⟩
  subst hR
  have hown : ∀ r ∈ S.base.rounds.zip S.stored, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n :=
    fun r hr' => own_of_ok (inFile S.base) hokb r.1 (List.of_mem_zip hr').1
  obtain ⟨rc, g1, g2, g3, g4, g5⟩ := foldX_facts (Fmt.HO O) S.base.cfg S.base.statement S.base.plan
    R b (S.base.rounds.zip S.stored) _ s hown hf
  have hlen := specX_len S hSok
  have hfst : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (le_of_eq hlen.symm)
  have hsnd : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (le_of_eq hlen)
  rw [hfst] at g2 g3
  have g1' : s.out.toList = rc.map roundWithStoredOpenings := by simpa using g1
  have ht : ((rc.map fun p => stripR p.1).toArray).toList = rc.map fun p => stripR p.1 := by simp
  have hF : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc := by
    rw [← hsnd]
    exact List.forall₂_map_left_iff.2 (g5.imp fun _ _ hh => hh.2)
  have hfull : everyOpeningHasItsDraws (xdOf S stm).xs ((rc.map fun p => stripR p.1).map (·.drawn)) = true := by
    refine fullX_true S.stored _ ?_
    rw [← hsnd, List.map_map]
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
    refine (forall2_and_left g5 (specX_parts S hSok)).imp fun x p hh t ht' => ?_
    show t.lo + t.count ≤ p.1.drawn.poss.length
    rw [hh.1.1]
    exact hh.2 t ht'
  have hL : LaxFacts (Fmt.HO O) (inFile S.base)
      (ownOut (Fmt.HO O 169 0 1 Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) := by
    refine ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩
    · intro r hr'
      have hr2 : some r = some _ := hr'.symm.trans hrun
      rw [Option.some.inj hr2]
      exact hrho
    · show TraceL (Fmt.HO O) S.base.plan S.base.rounds
        ((rc.map fun p => stripR p.1).toArray).toList ⟨S.base.label, rho0, 0⟩ #[]
      rw [ht]
      exact g2
  exact verifyX_true (xdOf S stm) dec O hO r0 r1 h0 h1 hokb hst
    (beq_iff_eq.1 (Fmt.ok_cfg hbok))
    _ (ownOut (Fmt.HO O 169 0 1 Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) R rc ht g1' rfl rfl
    hL hpd
    (by
      show passL (Fmt.HO O) S.base.rounds ((rc.map fun p => stripR p.1).toArray).toList
        ⟨S.base.label, rho0, 0⟩ = true
      rw [ht]
      exact g3)
    (by
      show rootsAll (Fmt.HO O) S.base.cfg R ((rc.map fun p => stripR p.1).toArray).toList = true
      rw [ht]
      exact g4)
    hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').2⟩)
    (stoOK_of S stm O r0 r1 hSok _ rc g1' hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').1.2⟩)
      honce hroot)
    (by
      show everyOpeningHasItsDraws (xdOf S stm).xs (((rc.map fun p => stripR p.1).toArray).toList.map (·.drawn))
        = true
      rw [ht]
      exact hfull)
    hdec

end

/-- The limits within which a chain that opens stored tables is covered. They are the library's
(`Run.PQ.XD.ok`), with the random bytes in the file or given, and one more.
The library's on `S.base`: `Run.PQ.ok`, which is the test of OnBytes/Tie/Limits.lean (`within_iff`,
OnBytes/Tie/OneChain.lean).
The library's on the stored tables (`Run.PQ.okX`): a table is opened behind a round that is there,
and its depth is at most that round's `logN`; a round that opens stored tables opens no tree of the
chain's own, and its parts lie one behind the other and use up all draws; over the whole chain the
first table's openings come before the second's; the chain's own trees have numbers below 2^16.
The library's on the tables' shapes: all have one depth; their leaves have salts as long as the
chain's own; the tables are the statement's items 0 and 1.
The one more: each table is opened at most once. -/
def withinX (S : Fmt.SpecX) : Bool :=
  (xdOf S fun _ _ => ByteArray.empty).ok && !S.base.rand.isNone &&
    decide (S.stored.flatten.map (·.item == 1)).Nodup

/-- Within the limits, `S.base` is within the limits of OnBytes/Tie/OneChain.lean. -/
theorem within_of_withinX (S : Fmt.SpecX) (hw : withinX S = true) : within S.base = true := by
  unfold withinX at hw
  simp only [Bool.and_eq_true] at hw
  have hk := hw.1.1
  unfold XD.ok at hk
  simp only [Bool.and_eq_true] at hk
  unfold within
  rw [Bool.and_eq_true]
  exact ⟨hk.1.1, hw.1.2⟩

/-- Within the limits, the sizes that the hash's domain asks for follow from the description's
being in order, but for the file's own size. -/
theorem smallFX_of_withinX (S : Fmt.SpecX) (hS : S.ok = true) (hw : withinX S = true)
    (b : ByteArray) (hb : b.size + 16 ≤ 2 ^ 32 - 144) : smallFX S b = true := by
  unfold smallFX
  rw [Bool.and_eq_true, smallF_of_within S.base (within_of_withinX S hw) b hb]
  refine ⟨rfl, ?_⟩
  rw [List.all_eq_true]
  intro ts hts
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at ht
    cases ht
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, k3⟩, k4⟩, k5⟩, k6⟩, -⟩, -⟩, -⟩ := h.2 t ht
    unfold Run.smallSh
    unfold Fmt.depthOK at k3
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨by rw [k6]; decide, of_decide_eq_true k3⟩, k4⟩, k5⟩, Or.inr k6⟩

/-- "The compiled verifier accepts what was read", for a chain that opens stored tables. o is what
the strict reader has read of the chain. The library's typing makes a typed string from o, and on
that string the compiled verifier of one slot says yes, at the tag "link", under the two tables'
roots r0 and r1. The protocol is the one that the library makes from the description S and the
decision dec. The typed oracle functions are those that the format's hash induces. -/
def CompiledAcceptsX (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (r0 r1 : ByteArray) (o : Fmt.ChainOut) : Prop :=
  ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up,
    toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
      (xdOf S stm).xs dec o = some π ∧
    (verifyOneProtocol (lam := 256) (K := (xdOf S stm).K + 1) (L := (xdOf S stm).L dec)
      (256 + 8 * S.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up
      (wqX (xdOf S stm).C (xdOf S stm).K (chalP S.base.plan.field (xdOf S stm).K) (xdOf S stm).ds
        (xdOf S stm).a (xdOf S stm).xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec
        (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
      (famX (xdOf S stm) dec Fmt.oracle ((xdOf S stm).K + 1)) = true

/-- A chain that opens stored tables, read by the strict reader at the format's own hash, at any
byte and under any record of vertices, and on which the decision is yes. Then the library's typing
gives a typed string, and the library's verifier for such files (`Run.PQ.VX`) accepts it. The other
hypotheses: r0 and r1 have 32 bytes; the description is within the limits (`withinX`); its statement
is `stm r0 r1`; the statement's item of every table that is opened holds that table's root, r0 for
item 0 and r1 for item 1; and the sizes are within the hash's domain (`smallFX`). -/
theorem stored_VX (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (hsm : smallFX S b = true) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) Fmt.formatHash S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) :
    ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧ VX (xdOf S stm) dec r0 r1 π = true := by
  unfold withinX at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
  obtain ⟨⟨hok, hn⟩, honce⟩ := hw
  have hB : S.base.params.size ≤ 2 ^ 32 - 144 := by
    unfold smallFX smallF smallB at hsm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm
    exact hsm.1.1.1.1.1.1
  have hpd : Fmt.HO Fmt.oracle 169 0 1 Fmt.zero32 S.base.params
      = Fmt.paramsDigest S.base.params :=
    Fmt.HO_oracle 169 0 1 Fmt.zero32 S.base.params
      (dom0 169 1 S.base.params (by decide) (by decide) (by decide) hB)
  obtain ⟨π, t1, t2⟩ := stored_core S stm dec Fmt.oracle Fmt.size_oracle r0 r1 h0 h1 hok hn honce
    hst hroot hpd seen b i o j ((readChainX_HO S seen b i hsm).trans e) hdec
  refine ⟨π, t1, ?_⟩
  rw [vx_eq]
  exact (thin_verify Unit Unit 256 _ ((xdOf S stm).L dec)
    (famX (xdOf S stm) dec Fmt.oracle ((xdOf S stm).K + 1)) Unit _ _ 256 .link _ _ _ _
    (fun _ => none) (fun s => some (.inl s)) 0 _ () π).symm.trans t2

/-- The same, said of the compiled verifier itself. -/
theorem stored_compiled (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hw : withinX S = true) (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (hsm : smallFX S b = true) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) Fmt.formatHash S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) : CompiledAcceptsX S stm dec r0 r1 o := by
  obtain ⟨π, hty, t⟩ := stored_VX S stm dec r0 r1 h0 h1 hw hst hroot seen b i hsm o j e hdec
  exact ⟨π, hty, (vx_eq (xdOf S stm) dec r0 r1 π).symm.trans t⟩

/-- The same in the form that fits the program: a chain that was read in a session, with the fast
forms of hash, reader and record, and on whose view a decision says yes. -/
theorem readInX_compiled (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hw : withinX S = true) (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (s : Session) (b : ByteArray) (i : ℕ) (hsm : smallFX S b = true) (r : ChainRead)
    (s' : Session) (e : readIn S b i s = some (r, s')) (hdec : dec r.view = true) :
    CompiledAcceptsX S stm dec r0 r1 r.out := by
  obtain ⟨t1, t2⟩ := readIn_read S b i s s' r e
  rw [t2] at hdec
  exact stored_compiled S stm dec r0 r1 h0 h1 hw hst hroot s.seen b i hsm r.out r.next t1 hdec

end OnBytes.Tie

#print axioms OnBytes.Tie.readInX_compiled
#print axioms OnBytes.Tie.stored_VX
#print axioms OnBytes.Tie.stored_compiled
