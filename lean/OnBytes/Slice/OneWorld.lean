-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneWorld.lean: a checker that asks one random oracle, and a bound on the chance that
it says yes while the language fails on what is read off the maker's queries.

OnBytes/Slice/Experiment.lean bounds an experiment under the typed random oracles of the library's
compiler, with the library's compiled Link verifier as the judge. (Link: the protocol `L.link` of
the library's interface, on two committed strings.) This file has ONE oracle, a function on bit
strings, and any checker as the judge. One world: the bound and the checker's run stand under the
same drawn oracle.

The experiment. The oracle is drawn: each bit string's answer is uniform among the strings of lam
bits, and all answers are independent (`Rom.U`). A maker asks it and puts out a value. A checker
asks the same oracle, tosses no coin, and either refuses that value or returns two roots and a Link
string. The event: the checker returns something, and the pair of strings that is read off THE
MAKER's OWN QUERIES under the two roots is outside the language.

What is asked of the checker. `hfit`: for every oracle g, if the checker under g returns two roots
and a string, the compiled Link verifier accepts them under the typed oracle functions that are read
out of g through the implementation m. `hrt`: the two roots are those that a function `rts` reads
off the maker's output. Beside that, only that it tosses no coin and that one number tR bounds its
queries on every output of the maker. What it reads and how it decides is free.

How it is proved. The library implements a family of typed oracles by one oracle on bit strings
(`Rom.OracleCoding`, Rom/Family.lean) and brings an algorithm over the one oracle down to the family
(`Rom.down m`: each string that it asks becomes one query at the typed point for which the string
stands, and of the answer it keeps that one block). The compiler's conclusion `LinkAt` has a clause
on stability: outside the bad set, what is read off a trace under a root that was announced in it
does not change when the trace grows. In the proof, and nowhere in a statement on one oracle, a
typed algorithm is put together from the maker, an announcement of the two roots (two queries to the
marker oracle `ann`, which stands for no hash call and off which nothing is read), the checker and
the compiled verifier. So the bound counts two queries more, and the compiled verifier's.

Main definitions: `runSel`, `annTr`, `announce`, `joinedSel`, `twoExp`, `twoWin`, `twoWinOne`.
Main theorems.
 `short_typed`     under the typed random oracles, for an algorithm in two phases.
 `twoExpOne_glue`  the experiment over the one oracle that holds all of a family F is the typed one
                   under F with both phases brought down, as to the outputs and the one-block
                   entries of the first phase's trace.
 `one_world`       with probability at most
                   (t + 2 + tR + tV) * e + 2 (t + 2 + tR + tV + 1)^2 / 2^lam the event happens.
                   t bounds the maker's queries and tR the checker's, both in strings put to the
                   one oracle, a repeated one counted again; tV is
                   `tVQB W.Lk W.depthReq`, the library's bound on the compiled verifier's typed
                   queries, a long answer counted once. In the code e is `εs`.

What is not claimed. That any checker meets `hfit`; that an implementation m exists for a given
interface (it is a one-to-one match of ALL bit strings with all blocks of all typed points, the
oracles that no algorithm of the scheme asks among them); that any m spells a typed query as a
program's hash call. Checker and m are variables here. A digest in an entry is the oracle's answer
read through m's match of answers, `m.rng`, which need not be the identity. Of the one-block entries
the reading takes those at the leaf and the node oracle. Where the maker's queries determine no
symbol at a place, the string has the library's fixed filling there. A checker that always refuses
meets `hfit`, and the event is then empty; so does a checker that says yes under few oracles only,
and the bound is then worth little. Nothing here says that a checker says yes on anything under a
drawn oracle.
The two roots are the maker's choice and are tied to nothing published. Nothing here reads bytes.
Nothing on the program, which is the Lean port built from OnBytes/, on the C++ verifier or on
BLAKE2b. The bound says nothing once it reaches 1. All content lies in `LinkAt W Lg e` at a named
language and a small e.

-/
import OnBytes.Slice.Experiment
import Compile.Batch.Local
import Rom.ExitBind

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {β δ : Type}

/-! ## Algorithms without coins, under fixed oracles -/

/-- An algorithm with a bound in the sense of `DetBound` tosses no coin. -/
theorem noCoin_of_detBound {S : OSpec} {α : Type} (c : OComp S α) :
    ∀ t : ℕ, DetBound c t → c.NoCoin := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | query o q k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => ih r t (h r)
  | sample n k _ => exact fun _ h => h.elim

/-- Under fixed oracles, what an algorithm without coins puts out beside its trace is its one
value. -/
theorem fst_of_mem_support {S : OSpec} {α : Type} (g : Fam S) (c : OComp S α) (hc : c.NoCoin)
    (o : α × Trace S) (ho : o ∈ (c.withTrace.runEager g).support) : o.1 = c.det g := by
  have h1 : o.1 ∈ ((c.withTrace.runEager g).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨o, ho, rfl⟩
  rw [runEager_withTrace_fst, hc.runEager g, PMF.support_pure] at h1
  exact h1

/-! ## The compiled verifier on a selection -/

/-- The compiled Link verifier with the strict format (sMT: bits of a leaf's salt; sFS: bits of the
chain's salt) on two roots and a Link string; "no" where there are none. -/
def runSel (W : QueryLayout lam L) (sMT sFS : ℕ) : Option (LinkOut lam L) → TypedOracleComputation lam W.K L Bool
  | none => OComp.pure false
  | some o => vLS W sMT sFS o.1 o.2.1 o.2.2

/-- `runSel` tosses no coin and asks at most the library's bound on the verifier's queries. -/
theorem detBound_runSel (W : QueryLayout lam L) (sMT sFS : ℕ) :
    ∀ y : Option (LinkOut lam L), DetBound (runSel W sMT sFS y) (tVQB W.Lk W.depthReq)
  | none => trivial
  | some o => detBound_vLS W sMT sFS o.1 o.2.1 o.2.2

/-! ## The marker oracle -/

/-- The entries that an announcement of two roots leaves in a trace; none where there are none. -/
def annTr (W : QueryLayout lam L) : Option (Dig lam × Dig lam) → Tc W
  | none => []
  | some r => [annE W r.1 (), annE W r.2 ()]

/-- Announces two roots: two queries to the marker oracle. -/
def announce (W : QueryLayout lam L) : Option (Dig lam × Dig lam) → TypedOracleComputation lam W.K L Unit
  | none => OComp.pure ()
  | some r => OComp.query (S := spec lam W.K L) Batch.OracleName.ann r.1 fun _ =>
      OComp.query (S := spec lam W.K L) Batch.OracleName.ann r.2 fun _ => OComp.pure ()

/-- The run of `announce` under fixed oracles, with its trace. -/
theorem announce_run (W : QueryLayout lam L) (F : Fam (spec lam W.K L)) :
    ∀ y : Option (Dig lam × Dig lam),
      (announce W y).withTrace.runEager F = PMF.pure ((), annTr W y)
  | none => rfl
  | some _ => rfl

/-- `announce` asks at most twice. -/
theorem announce_queryBound (W : QueryLayout lam L) :
    ∀ y : Option (Dig lam × Dig lam), (announce W y).QueryBound 2
  | none => trivial
  | some _ => fun _ _ => trivial

/-- An announcement behind a trace changes nothing that is read off it. -/
theorem extEnc_append_ann (W : QueryLayout lam L) (tr : Tc W) (cm : Dig lam) :
    ∀ y : Option (Dig lam × Dig lam), extEnc W (tr ++ annTr W y) cm = extEnc W tr cm
  | none => by rw [annTr, List.append_nil]
  | some r => by
    have e : tr ++ annTr W (some r) = (tr ++ [annE W r.1 ()]) ++ [annE W r.2 ()] := by
      simp [annTr]
    rw [e, Batch.extEnc_ann, Batch.extEnc_ann]

/-! ## Two phases, under the typed oracles -/

/-- **The experiment in two phases**: a first algorithm, whose trace is kept; then a second one on
its output. -/
def twoExp {S : OSpec} (B1 : OComp S β) (B2 : β → OComp S δ) : OComp S ((β × Trace S) × δ) :=
  B1.withTrace.bind fun x => (B2 x.1).bind fun y => OComp.pure (x, y)

/-- **The event**: `sel` reads two roots and a Link string off the two outputs, and the pair of
strings that is read off the FIRST phase's trace under the two roots is outside the language. -/
def twoWin (W : QueryLayout lam L) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop)
    (sel : β → δ → Option (LinkOut lam L)) : Set ((β × Tc W) × δ) :=
  {z | ∃ o, sel z.1.1 z.2 = some o ∧ ¬ Lg () (extEnc W z.1.2 o.1, extEnc W z.1.2 o.2.1)}

/-- The algorithm of the proof: the first phase, the announcement of the roots, the second phase,
the compiled Link verifier. It stands in no statement. -/
def joinedSel (W : QueryLayout lam L) (sMT sFS : ℕ) (B1 : TypedOracleComputation lam W.K L β)
    (rts : β → Option (Dig lam × Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ)
    (sel : β → δ → Option (LinkOut lam L)) : TypedOracleComputation lam W.K L Unit :=
  B1.bind fun b => (announce W (rts b)).bind fun _ => (B2 b).bind fun d =>
    (runSel W sMT sFS (sel b d)).bind fun _ => OComp.pure ()

/-- The algorithm of the proof asks at most t1 + 2 + t2 + tV queries. -/
theorem joinedSel_queryBound (W : QueryLayout lam L) (sMT sFS : ℕ) {B1 : TypedOracleComputation lam W.K L β}
    (rts : β → Option (Dig lam × Dig lam)) {B2 : β → TypedOracleComputation lam W.K L δ}
    (sel : β → δ → Option (LinkOut lam L)) {t1 t2 : ℕ} (h1 : B1.QueryBound t1)
    (h2 : ∀ b, (B2 b).QueryBound t2) :
    (joinedSel W sMT sFS B1 rts B2 sel).QueryBound (t1 + 2 + t2 + tVQB W.Lk W.depthReq) := by
  have h : (joinedSel W sMT sFS B1 rts B2 sel).QueryBound
      (t1 + (2 + (t2 + (tVQB W.Lk W.depthReq + 0)))) :=
    h1.bind fun b => (announce_queryBound W (rts b)).bind fun _ => (h2 b).bind fun d =>
      (detBound_runSel W sMT sFS (sel b d)).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- **The bound in two phases, under the typed random oracles.** Asked, beside `LinkAt W Lg e` and a
wiring in order (`hP`): under every family F, on all outputs that the two phases can have under F,
what `sel` reads off them the compiled Link verifier accepts under F, and its two roots are those
that `rts` reads off the first phase's output. Then with probability at most
(t1 + 2 + t2 + tV) * e + 2 (t1 + 2 + t2 + tV + 1)^2 / 2^lam the pair of strings that is read off the
first phase's trace under these roots is outside the language. tV is `tVQB W.Lk W.depthReq`, the
library's bound on the verifier's queries. The 2 stands for two queries to the marker oracle in the
proof. The bound says nothing once it reaches 1. -/
theorem short_typed (W : QueryLayout lam L) (hW : W.OKG) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop)
    (εs : ℝ≥0∞) (h : LinkAt W Lg εs) (sMT sFS : ℕ) (B1 : TypedOracleComputation lam W.K L β)
    (rts : β → Option (Dig lam × Dig lam)) (B2 : β → TypedOracleComputation lam W.K L δ)
    (sel : β → δ → Option (LinkOut lam L)) (t1 t2 : ℕ) (h1 : B1.QueryBound t1)
    (h2 : ∀ b, (B2 b).QueryBound t2)
    (hP : ∀ (F : Fam (spec lam W.K L)), ∀ x ∈ (B1.withTrace.runEager F).support,
      ∀ y ∈ ((B2 x.1).withTrace.runEager F).support, ∀ o, sel x.1 y.1 = some o →
        (vLS W sMT sFS o.1 o.2.1 o.2.2).det F = true ∧ rts x.1 = some (o.1, o.2.1)) :
    Rom.Pr (twoExp B1 B2) (fun _ => twoWin W Lg sel) ≤
      ((t1 + 2 + t2 + tVQB W.Lk W.depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t1 + 2 + t2 + tVQB W.Lk W.depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  obtain ⟨Bad, hrare, -, hL, hst⟩ := h
  refine le_trans ?_ (hrare _ (joinedSel W sMT sFS B1 rts B2 sel) _
    (joinedSel_queryBound W sMT sFS rts sel h1 h2))
  rw [← Pr_eq_law]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  simp only [twoExp, joinedSel, Compile.withTrace_bind, OComp.bind_assoc, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, announce_run, PMF.pure_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun x hx => ?_
  rw [← runEager_withTrace_fst F (B2 x.1), PMF.bind_map]
  refine pr_bind_le_bind _ _ _ _ _ fun y hy => ?_
  show pr (PMF.pure (x, y.1)) (twoWin W Lg sel) ≤ _
  rw [← PMF.bind_const ((runSel W sMT sFS (sel x.1 y.1)).withTrace.runEager F)
    (PMF.pure (x, y.1))]
  refine pr_bind_le_bind _ _ _ _ _ fun c hc => pr_pure_le_pure ?_
  rintro ⟨o, ho, hbad⟩
  have ho' : sel x.1 y.1 = some o := ho
  obtain ⟨hdet, hr⟩ := hP F x hx y hy o ho'
  show Bad (x.2 ++ (annTr W (rts x.1) ++ (y.2 ++ (c.2 ++ []))))
  by_contra hnb
  rw [ho'] at hc
  have hc' : c ∈ ((vLS W sMT sFS o.1 o.2.1 o.2.2).withTrace.runEager F).support := hc
  have hc1 : c.1 = true :=
    (fst_of_mem_support F _ (noCoin_of_detBound _ _ (detBound_vLS W sMT sFS o.1 o.2.1 o.2.2)) c
      hc').trans hdet
  have hrun : RunsIn c.2 (vLS W sMT sFS o.1 o.2.1 o.2.2) true := by
    have h3 := runsIn_of_mem_support (detBound_vLS W sMT sFS o.1 o.2.1 o.2.2) F c hc'
    rwa [hc1] at h3
  obtain ⟨π', hπ'⟩ := vL_of_vLS W hW (hrun.mono (fun e he =>
    List.mem_append_right x.2 (List.mem_append_right _ (List.mem_append_right y.2
      (List.mem_append_left [] he)))))
  have hfull := hL _ _ _ π' hnb hπ'
  have eassoc : x.2 ++ (annTr W (rts x.1) ++ (y.2 ++ (c.2 ++ []))) =
      (x.2 ++ annTr W (rts x.1)) ++ (y.2 ++ (c.2 ++ [])) := (List.append_assoc _ _ _).symm
  rw [eassoc] at hnb hfull
  have ha1 : Batch.Announced W (x.2 ++ annTr W (rts x.1)) o.1 := by
    rw [hr]
    exact List.mem_append_right _ List.mem_cons_self
  have ha2 : Batch.Announced W (x.2 ++ annTr W (rts x.1)) o.2.1 := by
    rw [hr]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [← hst _ _ o.1 hnb ha1, ← hst _ _ o.2.1 hnb ha2, extEnc_append_ann, extEnc_append_ann]
    at hfull
  exact hbad hfull

/-! ## Over one oracle -/

/-- **The event over one oracle**: `sel` reads two roots and a Link string off the two outputs, and
the pair of strings that is read off the one-block entries of the FIRST phase's trace under the two
roots is outside the language. -/
def twoWinOne (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (sel : β → δ → Option (LinkOut lam L)) :
    Set ((β × Trace (rom lam)) × δ) :=
  {z | ∃ o, sel z.1.1 z.2 = some o ∧
    ¬ Lg () (extEnc W (singleTr m z.1.2) o.1, extEnc W (singleTr m z.1.2) o.2.1)}

/-- For every family F: the outputs of the two phases over the one oracle that holds all of F, with
the one-block entries of the first phase's trace, are those of the two phases brought down, under
F. -/
theorem twoExpOne_glue {S : OSpec} (m : OracleCoding S lam) (B1 : OComp (rom lam) β)
    (B2 : β → OComp (rom lam) δ) (F : Fam S) :
    ((twoExp B1 B2).runEager (glue m F)).map (fun z => ((z.1.1, singleTr m z.1.2), z.2)) =
      ((twoExp (down m B1) fun b => down m (B2 b)).runEager F).map
        fun z => ((z.1.1, single m z.1.2), z.2) := by
  unfold twoExp
  simp only [OComp.runEager_bind, OComp.runEager, withTrace_down, runEager_down, PMF.map_bind,
    PMF.bind_map, PMF.pure_map, Function.comp_def, single_upTr]
  rw [bind_retr]

/-- Under fixed oracles F, what an algorithm without coins over the one oracle puts out when it is
brought down is its one value under the one oracle that holds all of F. -/
theorem fst_down_of_mem_support {S : OSpec} {α : Type} (m : OracleCoding S lam) (F : Fam S)
    (c : OComp (rom lam) α) (hc : c.NoCoin) (o : α × Trace S)
    (ho : o ∈ ((down m c).withTrace.runEager F).support) : o.1 = c.det (glue m F) := by
  have h1 : o.1 ∈ (((down m c).withTrace.runEager F).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨o, ho, rfl⟩
  rw [runEager_withTrace_fst, runEager_down, hc.runEager _, PMF.support_pure] at h1
  exact h1

/-- Whether the event holds is read off the one-block entries of the typed trace alone. Asked of m:
a leaf's and a node's answer is one block. -/
theorem twoWin_single (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (hl : m.blocks Batch.OracleName.leaf = 1) (hn : m.blocks Batch.OracleName.node = 1)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (sel : β → δ → Option (LinkOut lam L)) :
    twoWin W Lg sel =
      (fun z : (β × Tc W) × δ => ((z.1.1, single m z.1.2), z.2)) ⁻¹' twoWin W Lg sel := by
  ext z
  simp only [twoWin, Set.mem_setOf_eq, Set.mem_preimage, extEnc_single W m hl hn]

/-- **One world.** The oracle is a function from all bit strings to strings of lam bits, each value
drawn uniformly and independently. A maker with at most t queries puts out a value. A checker
without coins, with at most tR queries to the same oracle, refuses it or returns two roots and a
Link string. With probability at most
(t + 2 + tR + tV) * e + 2 (t + 2 + tR + tV + 1)^2 / 2^lam the checker returns something while the
pair of strings that is read off the one-block entries of THE MAKER's OWN TRACE under the two roots
is outside the language. t and tR count strings put to the oracle, a repeated one again; tV is
`tVQB W.Lk W.depthReq`, the library's bound on the compiled verifier's typed queries. Asked: the
wiring is in order (`W.OKG`); `LinkAt W Lg e`; in m a leaf's and a node's answer is one block;
`hfit`: under every oracle g, the compiled Link verifier accepts what the checker returns, under the
family that is read out of g through m; `hrt`: the roots that the checker returns are those that
`rts` reads off the maker's output. `hfit` is an assumption on the checker, and checker and m are
variables: that any checker meets it, or says yes on anything, is not shown. The roots are the
maker's choice. All content lies in `LinkAt` at a named language and a small e; the bound says
nothing once it reaches 1. Nothing on bytes, on the program, on BLAKE2b or on the C++ verifier. -/
theorem one_world {γ : Type} (W : QueryLayout lam L) (hW : W.OKG)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (h : LinkAt W Lg εs) (sMT sFS : ℕ)
    (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks Batch.OracleName.leaf = 1)
    (hn : m.blocks Batch.OracleName.node = 1) (chk : γ → OComp (rom lam) (Option (LinkOut lam L)))
    (rts : γ → Option (Dig lam × Dig lam)) (tR : ℕ) (hnc : ∀ x, (chk x).NoCoin)
    (hq : ∀ x, (chk x).QueryBound tR)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : LinkOut lam L), (chk x).det g = some o →
      (vLS W sMT sFS o.1 o.2.1 o.2.2).det (readBlocks m g) = true)
    (hrt : ∀ (g : Fam (rom lam)) (x : γ) (o : LinkOut lam L), (chk x).det g = some o →
      rts x = some (o.1, o.2.1))
    (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr (twoExp A chk) (fun _ => twoWinOne W m Lg fun _ y => y) ≤
      ((t + 2 + tR + tVQB W.Lk W.depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + 2 + tR + tVQB W.Lk W.depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have e1 : twoWinOne W m Lg (fun (_ : γ) (y : Option (LinkOut lam L)) => y) =
      (fun z : (γ × Trace (rom lam)) × Option (LinkOut lam L) =>
        ((z.1.1, singleTr m z.1.2), z.2)) ⁻¹' twoWin W Lg fun _ y => y := rfl
  have hF : ∀ F : Fam (spec lam W.K L),
      PrCoins (glue m F) (twoExp A chk) (twoWinOne W m Lg fun _ y => y) =
        PrCoins F (twoExp (down m A) fun b => down m (chk b)) (twoWin W Lg fun _ y => y) :=
    fun F => by
      unfold PrCoins
      rw [e1, ← pr_map, twoExpOne_glue, pr_map, ← twoWin_single W m hl hn Lg]
  have hP : Rom.Pr (twoExp A chk) (fun _ => twoWinOne W m Lg fun _ y => y) =
      Rom.Pr (twoExp (down m A) fun b => down m (chk b)) (fun _ => twoWin W Lg fun _ y => y) := by
    unfold Rom.Pr
    rw [lintegral_glue m (fun g => PrCoins g (twoExp A chk) (twoWinOne W m Lg fun _ y => y))]
    · simp only [hF]
    · simp only [hF]
      exact measurable_PrCoins _ _
  rw [hP]
  refine short_typed W hW Lg εs h sMT sFS (down m A) rts (fun b => down m (chk b))
    (fun _ y => y) t tR (queryBound_down m A t hA) (fun b => queryBound_down m (chk b) tR (hq b))
    fun F x _ y hy o ho => ?_
  have hy1 : y.1 = (chk x.1).det (glue m F) := fst_down_of_mem_support m F _ (hnc x.1) y hy
  have hd : (chk x.1).det (glue m F) = some o := hy1.symm.trans ho
  refine ⟨?_, hrt (glue m F) x.1 o hd⟩
  have h3 := hfit (glue m F) x.1 o hd
  rwa [readBlocks_glue] at h3

end OnBytes.Slice
