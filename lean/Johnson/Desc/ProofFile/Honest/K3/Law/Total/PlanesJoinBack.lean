-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/PlanesJoinBack.lean: the kind "lookup" (K3): for the item
"totalB" at the batching. Conditional: at an entry at which a link states the lookup's run "planes",
or its run "join", the run's values are the values of the item's forms, as an equation of lists; so
where the table's item at that entry holds, every coefficient of the run's terms is 0. This is the
reverse of the library's clauses `item_planes_unit` (Johnson/P1K9R/ItemPlanes.lean) and `item_join`
(Johnson/P1K9R/ItemJoin.lean), which state the inclusion alone. Five theorems, general in the
lookup's accessors and in the caller's readers and keys. The counterpart of
Honest/K3/Law/Total/ObjectsBack.lean.

Terms. Honest/K3/GLOSSARY.md. In this file: an entry o is a pair of a piece's number and a run's
name. `At L o run` (Johnson/Desc/First/Link/Law/LinkJoinPay.lean) says that the link L states the
run at the entry o. What is fixed at a state s is `fixed9 φ s`
(Johnson/Desc/First/Batch/Law/FitsAtS.lean). The link's reader is `K9.readersOfLink H L`
(Johnson/Desc/First/Batch/ReadersOfLink.lean); H holds its holes (`K9.LinkHoles`, there), and the
second hole is the field silent. The table's item at the entry is `formsQ`
(Johnson/Desc/Sound/FormsQ.lean), its public test `K9.formsIn`. The lookups' promise at what is
fixed is `K3Ok` (Johnson/Top/H/Keep/RunsPlain.lean).

What is shown.
  `back_of_values`: where a list of values is the list of the values of the forms of an item that
    holds, every coefficient of its plain terms (`plainTm`,
    Johnson/Desc/First/Batch/Law/PlainRuns.lean) is 0.
  `planes_values`, `planes_back`: the equation of lists and the reverse of the library's clause, at
    "planes" (`planesRun`, Johnson/Desc/First/Look/K3Runs.lean; the values `plVals`,
    RunsPlain.lean).
  `join_values`, `join_back`: the same at "join" (`K3.joinRun`, K3Runs.lean; the values `jnVals`,
    RunsPlain.lean).
The statements are sentences on the verifier's state and the library's terms: no prover, coin or
play is named.

Hypotheses that remain.
  `hn`, `hAt`: the entry's name is not "K8.equations"; the run stands at the entry.
  `hA`, `hs`: the accessors are the state's own (`AtS2`, Johnson/Top/H/Keep/RunsAtS.lean) and fit
    each other (`SeatFits`, Johnson/Top/H/K3RunsLaw.lean).
  `hφh`: what the lookup has heard is read off the fixed part.
  `hb`: a part is there at s (in `back_of_values` too).
  `hk`: `K3Ok` at what is fixed.
  `hsil`: the readers' second hole says nothing at the entry and the state.
  `hin`, `hq`: the table's public test at the entry holds (in the two equations); the table's item
    holds there (in the two reverses and in `back_of_values`).
  `ht`: (in the two reverses) the table of terms at the entry is `plainTm` of the run's values.
  `hR`, `hv`: (in `back_of_values`) the reader answers R at the entry; the list of values is the
    list of the values of R's forms.
  `hB`, `hP`, `hkv`: the caller's clauses: what the caller's forms on the planes' columns are worth
    (`hB`, `hP`), and what its key forms are worth (`hkv`). They remain hypotheses, as in the
    library: they are the calling kind's, for the attention's or the head's readers and keys. `hB`
    and `hP` are asked at every ledger later than the part's, as the library asks them; the proof
    uses them at one: the ledger behind the run.

How the proof goes. The library's own two proofs, followed to the equations that they hold on their
way.

Users. `planes_back_fam` and `join_back_att` (Honest/K3/Law/Total/CallersPaid.lean) call
`planes_back` and `join_back`, and show the caller's clauses at the attention's and the head's
readers and keys.

Kin. The library's word for an equation of lists at an item is `ItemAt`, with `ItemAt.toIn`
(Johnson/Desc/First/Link/Law/HitemsStill.lean): `planes_values` and `join_values` state its third
conjunct and its last in a shape of their own.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not reached: the entry "join" of the head's segment, whose terms are the caller's own table's.
At the head's segment `hsil` cannot be had at the library's own holes (`K9.holesAt`,
Johnson/Desc/First/Batch/ReadersAt.lean) at a state at which the tables can be made and the run
answers: there the second hole is filled (`k6Silent`, Johnson/Desc/Kinds/Law/K6SilentCode.lean: the
run itself at the state with the tables laid), at every name of a run; where the tables cannot be
made at the state, or the run refuses there, that hole says nothing. There the lemma is meant at the
empty hole (`K9.withSmall K9.LinkHoles.none`, Johnson/Desc/First/Batch/SmallReader.lean: `hsil` by
`rfl`), and what it says is carried over to the library's holes by the library's `forms_of_run`
(Johnson/Desc/First/Link/Law/HitemsHead.lean), where the run's own reader answers at the state. That
carrying over is not made here, and that hypothesis of `forms_of_run` is not shown in this file. At
every other segment the library's second hole says nothing outright. This bears on the head's entry
"planes". By a count over the table's text, not by Lean: of the nine
entries of "totalB" at which a link states one of the lookup's runs (six "objects", two "planes",
attention's "join") three are the head's (two "objects", one "planes"): so at the library's own
holes the theorems of Honest/K3/Law/Total/ObjectsBack.lean and
Honest/K3/Law/Total/PlanesJoinBack.lean apply at six of the nine. The nine are written out, by the
link's sort, in the statements of `theta_at_layers`, `theta_at_attention` and `theta_at_head`
(Honest/K3/Law/ThetaKept.lean).
The library has other theorems of the short names `planes_back`
(Johnson/Top/H/Keep/HeadHoleFwd.lean) and `join_back` (Johnson/Top/H/Keep/HeadOwnAtSeat.lean). These
are `ProofFile.Honest.K3.Law.Total.planes_back` and `ProofFile.Honest.K3.Law.Total.join_back`.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P1K9R.ItemPlanes
import Johnson.P1K9R.ItemJoin
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K4Values (refWorld)
open VerifiableInference.OnPublicFiles (AtS2 SeatFits plVals jnVals K3Ok pick_some pick_spec planes_heard
        planes_worth bitOf pinOf fork_of_atS join_heard joinRun_cut join_worth keysOf lateOf_same)

variable {α : Type}

/-- Where the values of a run are the values of the forms of an item that holds, every coefficient
of the run's plain terms is 0. -/
theorem back_of_values (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (vals : α × Option Pub9 → Bound Cb.Gl.E → List Cb.Gl.E) (q : α × Option Pub9) (R : K9.Read)
    (hR : Rd.forms o.1 o.2 s = some R)
    (hv : vals q (dataQ own b rd) =
      R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b rd)))
    (hq : formsQ Rd own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ plainTm vals n q (dataQ own b rd), c.2 = 0 := by
  obtain ⟨a', R', ha', hR', -, hf⟩ := hq
  obtain rfl : a' = b := Option.some.inj (ha'.symm.trans (K9.segAt_of_atS s b hb))
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  intro n c hc
  have h1 : c.2 ∈ (plainTm vals n q (dataQ own a' rd)).map (·.2) :=
    List.mem_map.2 ⟨c, hc, rfl⟩
  rw [show (plainTm vals n q (dataQ own a' rd)).map (·.2) = vals q (dataQ own a' rd)
    from numbered_snd _ n, hv] at h1
  obtain ⟨f, hfm, e⟩ := List.mem_map.1 h1
  rw [← e]
  exact (hf f hfm).2

/-! ## "planes" -/

/-- **The equation of lists at "planes".** Conditional on what this file's head lists, and on the
table's public test at the entry. No instance of these hypotheses is exhibited in this file. -/
theorem planes_values (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (readers : K3.Readers S)
    (bv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → ℕ → Cb.Gl.E)
    (pv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → Cb.Gl.E)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun seat lm readers))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 s = true)
    (hB : ∀ G, _root_.Fo.Later b.F G → ∀ k col,
      (bitOf readers s k col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b rd).mask
          (entUnit (fixed9 φ s) (dataQ own b rd))) =
        bv (fixed9 φ s) (dataQ own b rd) k col)
    (hP : ∀ G, _root_.Fo.Later b.F G → ∀ col,
      (pinOf readers s col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b rd).mask
          (entUnit (fixed9 φ s) (dataQ own b rd))) =
        pv (fixed9 φ s) (dataQ own b rd) col) :
    ∃ R, (K9.readersOfLink H L).forms o.1 o.2 s = some R ∧
      plVals hd lm jLK bv pv (fixed9 φ s) (dataQ own b rd) =
        R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b rd)) := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt s hsil R hR
  obtain ⟨F1, g, -, e2⟩ := planes_heard seat lm readers (l := z.1) (s' := z.2) hz
  obtain rfl : G0 = b.F := Option.some.inj (hG0.symm.trans (fork_of_atS hb))
  have hfk : seat.fork s = some b.F := (hA.fork s).trans hG0
  have hq2 : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ s).1 = some g := by
    show hd (φ s) = _
    rw [← hφh]
    exact e2
  obtain ⟨su, ok, -⟩ := hk g (pubOf b) hg' hq2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  obtain ⟨G', f1, -, l1, -, -, hv⟩ := planes_worth seat (·.form) hs lm readers Cb.Gl.E Reading.gl g
    jLK rs0 F0 b.F 0 s z.2 z.1 e2 hfk hI hL ok su hz
  obtain rfl : G' = G := Option.some.inj (f1.symm.trans ((hA.fork z.2).trans hG))
  subst hRz
  have hval := hv G' (_root_.Fo.Later.refl G') (_root_.Fo.muOf (dataQ own b rd).mask)
    (entUnit (fixed9 φ s) (dataQ own b rd))
  have hlist : plVals hd lm jLK bv pv (fixed9 φ s) (dataQ own b rd) =
      z.1.map fun c => c.form.value Reading.gl
        (G'.worldOf Reading.gl (dataQ own b rd).mask
          (entUnit (fixed9 φ s) (dataQ own b rd))) := by
    have e0 : bv (fixed9 φ s) (dataQ own b rd) 0 = fun col =>
        (bitOf readers s 0 col).value Reading.gl (G'.worldOf Reading.gl
          (fun j => _root_.Fo.muOf (dataQ own b rd).mask (.mask j))
          (entUnit (fixed9 φ s) (dataQ own b rd))) :=
      (funext fun col => hB G' l1 0 col).symm
    have e1 : bv (fixed9 φ s) (dataQ own b rd) 1 = fun col =>
        (bitOf readers s 1 col).value Reading.gl (G'.worldOf Reading.gl
          (fun j => _root_.Fo.muOf (dataQ own b rd).mask (.mask j))
          (entUnit (fixed9 φ s) (dataQ own b rd))) :=
      (funext fun col => hB G' l1 1 col).symm
    have e3 : pv (fixed9 φ s) (dataQ own b rd) = fun col =>
        (pinOf readers s col).value Reading.gl (G'.worldOf Reading.gl
          (fun j => _root_.Fo.muOf (dataQ own b rd).mask (.mask j))
          (entUnit (fixed9 φ s) (dataQ own b rd))) :=
      (funext fun col => hP G' l1 col).symm
    unfold plVals
    rw [hp, e0, e1, e3]
    exact hval.symm
  refine ⟨_, hR, ?_⟩
  rw [hlist]
  show _ = (z.1.map (·.form)).map fun f =>
    f.value Reading.gl (worldOwn b (K9.lateOf b.F G') (dataQ own b rd))
  rw [List.map_map]
  refine List.map_congr_left fun c hc => ?_
  have hf : c.form ∈ z.1.map (·.form) := List.mem_map.2 ⟨c, hc, rfl⟩
  have haff : K9.affIn own (K9.mergeOf s) (K9.lateOf b.F G') b c.form = true := by
    have h0 := hin
    unfold K9.formsIn at h0
    rw [K9.segAt_of_atS s b hb, hR] at h0
    exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h0).2 c.form hf
  show _ = c.form.value Reading.gl (worldOwn b (K9.lateOf b.F G') (dataQ own b rd))
  rw [value_behind own (K9.mergeOf s) b G' l1 (dataQ own b rd) c.form haff]
  have hsw : c.form.value Reading.gl (G'.worldOf Reading.gl (dataQ own b rd).mask
        (worldOwn b (K9.lateOf b.F G') (dataQ own b rd)).entry) =
      c.form.value Reading.gl (G'.worldOf Reading.gl (dataQ own b rd).mask
        (entUnit (fixed9 φ s) (dataQ own b rd))) := by
    refine value_eq _ _ c.form (fun x hx => ?_) fun _ _ => rfl
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
      (named_of_formsIn _ own o.1 o.2 s b _ hb hR hin c.form hf x hx)
    exact (ent_meets b (K9.lateOf b.F G') (dataQ own b rd) (fixed9 φ s) hq2 x.tree x.row
      x.idx y hy).symm
  exact hsw.symm

/-- **The reverse of the library's clause at "planes".** Conditional on what this file's head lists.
No instance of these hypotheses is exhibited in this file. -/
theorem planes_back (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (readers : K3.Readers S)
    (bv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → ℕ → Cb.Gl.E)
    (pv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → Cb.Gl.E)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun seat lm readers))
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (ht : tmOf o = plainTm (plVals hd lm jLK bv pv))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd)
    (hB : ∀ G, _root_.Fo.Later b.F G → ∀ k col,
      (bitOf readers s k col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b rd).mask
          (entUnit (fixed9 φ s) (dataQ own b rd))) =
        bv (fixed9 φ s) (dataQ own b rd) k col)
    (hP : ∀ G, _root_.Fo.Later b.F G → ∀ col,
      (pinOf readers s col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b rd).mask
          (entUnit (fixed9 φ s) (dataQ own b rd))) =
        pv (fixed9 φ s) (dataQ own b rd) col) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 φ s) (dataQ own b rd), c.2 = 0 := by
  rw [ht]
  obtain ⟨R, hR, hv⟩ := planes_values H L φ hd lm jLK seat hA hs hφh readers bv pv own rd o hn hAt
    s b hb hk hsil (formsQ_in _ own o.1 o.2 s rd hq) hB hP
  exact back_of_values _ own rd o s b hb _ _ R hR hv hq

/-! ## "join" -/

/-- **The equation of lists at "join".** Conditional on what this file's head lists, and on the
table's public test at the entry. No instance of these hypotheses is exhibited in this file. -/
theorem join_values (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (keys : S → Option (Array Aff)) (kv : α × Option Pub9 → Bound GQ → ℕ → GQ)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (K3.joinRun seat keys))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 s = true)
    (hkv : ∀ k, ((keysOf keys s).getD k (Aff.ofConst zeroE)).value Reading.gl
      (refWorld Reading.gl b.F [] (entUnit (fixed9 φ s) (dataQ own b rd))
        (dataQ own b rd)) = kv (fixed9 φ s) (dataQ own b rd) k) :
    ∃ R, (K9.readersOfLink H L).forms o.1 o.2 s = some R ∧
      jnVals hd lm jLK kv (fixed9 φ s) (dataQ own b rd) =
        R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b rd)) := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  have hnamed := named_of_formsIn _ own o.1 o.2 s b R hb hR hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt s hsil R hR
  obtain ⟨F1, g, e1, e2⟩ := join_heard seat keys (l := z.1) (s' := z.2) hz
  obtain ⟨KF, -, -, hcl, hmk⟩ := joinRun_cut seat keys (cl := z.1) (s' := z.2) e1 e2 hz
  obtain rfl : G0 = F1 := Option.some.inj (hG0.symm.trans ((hA.fork s).symm.trans e1))
  obtain rfl : G0 = b.F := Option.some.inj (hG0.symm.trans (fork_of_atS hb))
  have hG' : G = b.F.paid g.owedJoin := by
    have h1 : (seat.mark s (b.F.paid g.owedJoin)).fork? = some (b.F.paid g.owedJoin) := by
      rw [hA.mark]
      exact fork_putFork s b.F hG0 _
    rw [hmk] at hG
    exact Option.some.inj (hG.symm.trans h1)
  have hlate : K9.lateOf b.F G = [] := by
    rw [hG']
    exact lateOf_same b.F _ rfl
  have hRz' : R = { forms := [Fo.joinForm g KF], late := [] } := by
    rw [hRz, hlate, hcl]
    show K9.Read.mk [(seat.claim (Fo.joinForm g KF)).form] [] = _
    rw [hA.form]
  subst hRz'
  have hq2 : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ s).1 = some g := by
    show hd (φ s) = _
    rw [← hφh]
    exact e2
  obtain ⟨su, okS, -⟩ := hk g (pubOf b) hg' hq2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  obtain ⟨G2, f2, -, -, -, -, hv⟩ := join_worth seat (·.form) hs lm keys GQ Reading.gl g jLK rs0 F0
    b.F 0 s z.2 z.1 e2 e1 hI hL okS su hz
  obtain rfl : G2 = b.F.paid g.owedJoin := by
    rw [hmk, hs.markFork s b.F _ e1] at f2
    exact (Option.some.inj f2).symm
  have hv' := hv _ (Fo.Later.refl _) (Fo.muOf (dataQ own b rd).mask)
    (entUnit (fixed9 φ s) (dataQ own b rd))
  rw [hcl] at hv'
  have hw : (b.F.paid g.owedJoin).worldOf Reading.gl
      (fun j => Fo.muOf (dataQ own b rd).mask (.mask j))
      (entUnit (fixed9 φ s) (dataQ own b rd)) =
      refWorld Reading.gl b.F [] (entUnit (fixed9 φ s) (dataQ own b rd))
        (dataQ own b rd) := by
    rw [refWorld_nil]
    rfl
  rw [hw] at hv'
  have hval : (Fo.joinForm g KF).value Reading.gl
      (refWorld Reading.gl b.F [] (entUnit (fixed9 φ s) (dataQ own b rd))
        (dataQ own b rd)) =
      Fo.claimJoin g.shape lm jLK rs0 (Fo.muOf (dataQ own b rd).mask)
        (kv (fixed9 φ s) (dataQ own b rd)) := by
    have h0 := List.head_eq_of_cons_eq hv'
    beta_reduce at h0
    rw [hA.form] at h0
    rw [h0]
    congr 1
    funext k
    exact hkv k
  refine ⟨_, hR, ?_⟩
  have hne := hnamed (Fo.joinForm g KF) (List.mem_singleton.2 rfl)
  unfold jnVals
  rw [hp]
  show [Fo.claimJoin g.shape lm jLK rs0 (Fo.muOf (dataQ own b rd).mask)
      (kv (fixed9 φ s) (dataQ own b rd))] =
    [(Fo.joinForm g KF).value Reading.gl (worldOwn b [] (dataQ own b rd))]
  rw [← value_meets_still b (dataQ own b rd) (fixed9 φ s) hq2 _ hne, hval]

/-- **The reverse of the library's clause at "join".** Conditional on what this file's head lists.
No instance of these hypotheses is exhibited in this file. -/
theorem join_back (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (keys : S → Option (Array Aff)) (kv : α × Option Pub9 → Bound GQ → ℕ → GQ)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (K3.joinRun seat keys))
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (ht : tmOf o = plainTm (jnVals hd lm jLK kv))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd)
    (hkv : ∀ k, ((keysOf keys s).getD k (Aff.ofConst zeroE)).value Reading.gl
      (refWorld Reading.gl b.F [] (entUnit (fixed9 φ s) (dataQ own b rd))
        (dataQ own b rd)) = kv (fixed9 φ s) (dataQ own b rd) k) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 φ s) (dataQ own b rd), c.2 = 0 := by
  rw [ht]
  obtain ⟨R, hR, hv⟩ := join_values H L φ hd lm jLK seat hA hs hφh keys kv own rd o hn hAt s b
    hb hk hsil (formsQ_in _ own o.1 o.2 s rd hq) hkv
  exact back_of_values _ own rd o s b hb _ _ R hR hv hq

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.back_of_values
#print axioms ProofFile.Honest.K3.Law.Total.planes_values
#print axioms ProofFile.Honest.K3.Law.Total.planes_back
#print axioms ProofFile.Honest.K3.Law.Total.join_values
#print axioms ProofFile.Honest.K3.Law.Total.join_back
