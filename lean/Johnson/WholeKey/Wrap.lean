-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Wrap.lean: THE SIMULATOR, A NAMED TERM: A REDUCTION AROUND A GAME OF THE
INTERACTIVE PROTOCOLS, for the scheme with the whole key published (argW,
Johnson/WholeKey/Defs.lean), over the typed oracles. AT LETTERS. DEFINITIONS ALONE.

General definitions. This file states no goal of the release, and it proves nothing.

The game (Hiop/Seeded/Game.lean) has no hash function in its protocol: a caller names a seed and
gets the out-of-domain answers of a fresh encoded index at that seed; it asks for a run of the test
on the first encoded index, of a link, of a session, and gets what such a run discloses (a view, or
"none"). There is a real game on an index i, played by the protocols' honest sides, and a simulated
game, which keeps encodings of a fixed index i₀ and answers by the simulators of the interactive
protocols.

THE REDUCTION (wrapW) does all the hash work of the scheme's committer and prover AND NEVER HOLDS AN
ENCODED INDEX, by type: it knows of a table its salts, its leaves' digests and the levels above
them, its seed and its out-of-domain answers; the body of a leaf is named only when a view brings
the symbol at an opened position (namedAt). It is a program over ANY game of that type (Rom.Wrap,
Compile/Step1_defc_Gen.lean). It keeps the oracle's table in its own state and never asks the game's
oracles.
  setup    the committer's coins; then, for each of the M + 2 tables: fresh digests for all leaves,
           the inner nodes and the seed's two queries asked of its own table, and the call "a table
           at this seed"; then the call for the test and, with what it discloses, PASS 2 of a
           simulated compiled run (Johnson/WholeKey/Sim.lean); then the same for each link.
  a request  the prover's coins; the call for a session on the drawn copy; pass 2.
  a query  lazy sampling from its table.
PASS 1 IS THE GAME's: each run of the game comes with an auxiliary value, drawn by the game, off
which the verifier messages are read. Here that value is (the outcome, the list of recorded answers)
of pass 1, the dry run of the compiled prover's chain (kitW). The dry run is made at blank letters
(no list of roots, blank coins with the right number of sibling digests). That its list of answers
serves for pass 2 at the run's own letters rests on a reading of the chain's text, which is NOT
PROVED here: which oracles the chain asks in which order, and what the verifier messages are, hangs
on the answers in their order, on the wire, on the caps and on the number of sibling digests alone.
A SEARCH THAT RUNS OUT. Where pass 1's outcome is "a search has run out" there are no verifier
messages: the game then shows nothing of the run and reads nothing, alike in the real and in the
simulated game, and the string is "none". Nothing in the premises on hiding bounds the chance of
that. With caps so small that every search runs out, every string is "none", and what a
statement of index privacy says OF THE RUNS is idle (the roots and the out-of-domain answers in the
key are still to be hidden): completeness at the same caps is what shuts that out.
THE GAME COUNTS: it refuses a call beyond its bounds (boundsW: one test, one link a copy, s1
sessions a copy) and a seed outside the public set Gs. Where the game refuses, the reduction hands
out "none", or, at the setup, a fixed key.

THE SIMULATOR (simWholeKey) is the reduction around the simulated game, in the library's form
(Compile.GlueB.simOf, Compile/Batch/SpecGlue.lean). WHAT IT IS HANDED: the public parameters and the
number of requests, neither of which it reads; each oracle query; for a request its instance.
NOTHING OF THE INDEX. Its letters: the honest side's public letters, the three simulators of the
interactive protocols (the session's: one for each number of a copy), A FIXED INDEX i₀, the number
s1 of sessions that a copy serves, the public set Gs of seeds. THE SEEDS ARE ASKED AS EVERYBODY ASKS
THEM; NOTHING IS PROGRAMMED AT A SEED's QUERIES; the key holds i₀'s own answers at the seeds that
come.
The public starts of salts: the chain is handed its coins with public starts in front of the leaves'
free bits (dress, Johnson/WholeKey/Defs.lean). The honest side makes the starts from strings that it
reads off its strategy's coins; the reduction reads them off THE VIEW's PLAIN PARTS (pvT, pvL, pvB).
At a stop the starts do not matter: no leaf of such a run is ever written.

Main names (namespace OnBytes.WholeKey).
  pass1, blank, kitW      the dry pass; blank coins; the game's auxiliary values.
  namedAt, pass2A         a kept tree with the opened leaves' bodies named; pass 2 as a program.
  TabW, tableA, tablesA   a table as the reduction keeps it; its making.
  linksA, setupA, proveStepA, wrapW   THE REDUCTION.
  simsG, boundsW, simWholeKey    the game's simulators and bounds; THE SIMULATOR.

Limits. Definitions alone. One request a proof.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Sim
import Rom.Handle.Adv
import Hiop.Seeded.Game
import Compile.Batch.SpecGlue

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The two passes, apart -/

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ)

/-- **Pass 1**, dry: the compiled prover's chain at the strategy of fixed messages; each late query
gets a fresh answer. The outcome, cut to the verifier messages, and the list of the answers. -/
def pass1 (co : Coins lam L) : PMF (Res (Rho Q.loc.shape) × Record (typedOracleFamily lam K L)) :=
  ((chainX t Q wq embS embP xin cms x cap (Strat.dflt _ ()) co).bind fun r =>
    .pure (r.map fun z => z.1)).record mkRun

/-- Kept trees with the bodies of the opened leaves named: at a leaf at which a position stands
whose symbol is given, the body is that symbol as the wire writes it; the salts, the other bodies
and the levels stay. -/
def namedAt (embE : E.Sym → Body L) (ans : E.Pos → Option E.Sym) : ℕ → TreeK lam L := fun k =>
  { xt k with
    inp := fun j =>
      match wq.ext.all.find? fun p =>
          decide (wq.ext.which p = k) && decide (wq.ext.leaf p = j) && (ans p).isSome with
      | some p => ⟨((ans p).map embE).getD ((xt k).inp j).body, ((xt k).inp j).salt⟩
      | none => (xt k).inp j }

/-- The external symbols that a view brings. -/
def ansOf (v : Option (DView Q.loc)) : E.Pos → Option E.Sym :=
  match v with
  | some d => d.ext
  | none => fun _ => none

/-- **Pass 2**, as a program against any challenger, which it neither asks nor calls: the chain at
the strategy made from the view, the late queries answered by the recorded list; then what is handed
out and the table (handOut, Johnson/WholeKey/Sim.lean), the external strings and the opened leaves'
bodies made from the view. -/
def pass2A {Out In : Type} (embE : E.Sym → Body L) (v : Option (DView Q.loc)) (co : Coins lam L)
    (Rc : Record (typedOracleFamily lam K L)) (T : Table (typedOracleFamily lam K L)) :
    Adv (typedOracleFamily lam K L) Out In (Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam K L)) :=
  ((chainX t Q wq embS embP xin cms x cap (stratFor Q wq v) co).runReplayA mkRun T [] Rc).bind
    fun o => .halt (handOut Q wq x (wq.ext.build (ansOf Q v))
      (namedAt Q wq xt embE (ansOf Q v)) v.isSome co o)

end Generic

/-! ## At an object with out-of-domain samples -/

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- Blank coins with dq sibling digests. -/
def blank (b₀ : Bd) (dq : ℕ) : Coins lam (typedOracleCarrier L Bd aT aL) :=
  ⟨[], fun _ _ _ _ => [], b₀, 0, List.replicate dq default, []⟩

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- **The game's auxiliary values**: for each of the three kinds of run (the outcome, the recorded
answers) of pass 1 at blank letters; the verifier messages are the outcome's, if the searches have
not run out. -/
def kitW : Hiop.Seeded.Kit L where
  AT := Res (Rho L.offline.shape) × Record (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
  AL := Res (Rho L.link.shape) × Record (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
  AB := Res (Rho L.onlineBatch.loc.shape) × Record (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
  μT := fun _ y => pass1 Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) [] y h.capT
    (blank h.b₀ W.depthReqT)
  μL := fun _ y => pass1 Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) [] y h.capL
    (blank h.b₀ W.depthReqL)
  μB := fun _ y => pass1 Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) [] y h.capB
    (blank h.b₀ W.depthReq)
  ρT := fun a => a.1.toOption
  ρL := fun a => a.1.toOption
  ρB := fun a => a.1.toOption

/-- The reduction's programs: over the scheme's oracles, with the game's calls and replies. -/
abbrev AdvG (α : Type) : Type :=
  Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (Hiop.Seeded.GOut L (kitW W r₀ h).form)
    (Hiop.Seeded.GIn L (kitW W r₀ h).form) α

/-- A table as the reduction keeps it: the tree (salts, digests of the leaves, the levels above; THE
BODIES IN IT ARE FILLINGS, not the encoded index), and the out-of-domain sample. -/
structure TabW (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  tree : TreeK lam (typedOracleCarrier L Bd aT aL)
  ood : L.Rec

/-- The making of a table: all leaves late (fresh digests; the bodies are fillings), the inner nodes
and the seed's two queries asked of the reduction's table; then the call "a table at this seed".
none: the game has refused. -/
def tableA (s : ℕ → Bits) (T : Tb W) : AdvG W r₀ h (Option (TabW lam L Bd aT aL) × Tb W) :=
  (((treeO W.depth fun j => (⟨h.b₀, s j⟩ : LeafIn (typedOracleCarrier L Bd aT aL))).bind fun tr =>
      (seedsO W S tr.root).bind fun e => .pure (tr, e)).runDeferA mkTab T []).bind fun o =>
    .call (.table o.1.2) fun a =>
      match a with
      | .ood rc => .halt (some ⟨o.1.1, rc⟩, o.2.1)
      | _ => .halt (none, o.2.1)

/-- Tables one after the other. none: the game has refused one. -/
def tablesA : List (ℕ → Bits) → Tb W → AdvG W r₀ h (Option (List (TabW lam L Bd aT aL)) × Tb W)
  | [], T => .halt (some [], T)
  | s :: ss, T => (tableA W S r₀ h s T).bind fun o =>
      (tablesA ss o.2).bind fun o' =>
        .halt (o.1.bind fun t => o'.1.map fun ts => t :: ts, o'.2)

/-- The entries of the key's list, one after the other: for the copy number e the call for its link,
then pass 2. -/
def linksA (t₁ : TabW lam L Bd aT aL) :
    ℕ → List (DrawCopy lam L Bd aT aL h.KL × TabW lam L Bd aT aL) → Tb W →
    AdvG W r₀ h (List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) × Tb W)
  | _, [], T => .halt ([], T)
  | e, a :: l, T =>
      .call (.link e) fun rp =>
        (match rp with
          | .link u =>
              pass2A Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
                (cmsLA cA t₁.tree.root a.2.tree.root t₁.ood.2 a.2.ood.2) (t₁.ood, a.2.ood)
                (fun k => if k = 0 then t₁.tree else a.2.tree) h.capL W.embE u.2
                (match u.2 with
                  | some d => h.dressL (h.pvL d.plains) a.1.co
                  | none => a.1.co) u.1.2 T
          | _ => .halt (none, T)).bind fun o =>
        (linksA t₁ (e + 1) l o.2).bind fun o' =>
          .halt ((a.2.tree.root, a.2.ood, o.1) :: o'.1, o'.2)

/-- The reduction's state: the oracle's table; after the setup the copies as it keeps them. -/
abbrev StG (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Type :=
  Tb W × Option (List (TabW lam L Bd aT aL))

/-- The setup. Where the game refuses a table: a fixed key, and nothing is served afterwards. -/
def setupA (T : Tb W) :
    AdvG W r₀ h (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W) :=
  ((coinsC W h).runLazyA T).bind fun o₀ =>
  (tableA W S r₀ h (cutS (2 ^ W.depth) o₀.1.s) o₀.2).bind fun o₁ =>
  (tablesA W S r₀ h (o₀.1.copies.map fun d => cutS (2 ^ W.depth) d.s) o₁.2).bind fun o₂ =>
  match o₁.1, o₂.1 with
  | some t₁, some ts =>
      .call (.test 0) fun rp =>
        (match rp with
          | .test u =>
              pass2A Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
                (cmsTA cA t₁.tree.root t₁.ood.2) t₁.ood (fun _ => t₁.tree) h.capT W.embE u.2
                (match u.2 with
                  | some d => h.dressT (h.pvT d.plains) o₀.1.co
                  | none => o₀.1.co) u.1.2 o₂.2
          | _ => .halt (none, o₂.2)).bind fun o₃ =>
        (linksA W cA r₀ h t₁ 1 (o₀.1.copies.zip ts) o₃.2).bind fun o₄ =>
          .halt (.inl ⟨t₁.tree.root, t₁.ood, o₃.1, o₄.1⟩, (o₄.2, some ts))
  | _, _ => .halt (.inl ⟨default, r₀, none, []⟩, (o₂.2, none))

/-- A batch: one request a proof. -/
def proveStepA (w : StG W) : List X →
    AdvG W r₀ h (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L) × StG W)
  | [] => .halt (.inr [], w)
  | [x] => ((coinsP W h).runLazyA w.1).bind fun o =>
      match w.2.bind fun ts => ts[o.1.j]? with
      | none => .halt (.inr [⟨o.1.j, h.nm o.1.j, none⟩], (o.2, w.2))
      | some t =>
        .call (.sess (o.1.j + 1) x ()) fun rp =>
          (match rp with
            | .sess _ u =>
                pass2A Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA t.tree.root t.ood.2)
                  (x, t.ood) (fun _ => t.tree) h.capB W.embE u.2
                  (match u.2 with
                    | some d => h.dressB (h.pvB d.plains) o.1.co
                    | none => o.1.co) u.1.2 o.2
            | _ => .halt (none, o.2)).bind fun o' =>
          .halt (.inr [⟨o.1.j, h.nm o.1.j, o'.1⟩], (o'.2, w.2))
  | u :: v :: l => .halt (.inr ((u :: v :: l).map fun _ => ⟨0, 0, none⟩), w)

/-- **THE REDUCTION.** -/
def wrapW : Rom.Wrap (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (Compile.GlueB.SCall X)
    (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L))
    (Hiop.Seeded.GOut L (kitW W r₀ h).form) (Hiop.Seeded.GIn L (kitW W r₀ h).form) where
  τ := StG W
  ans := fun w o q => (HandlerA.lazy w.1 o q).bind fun p => .halt (p.1, (p.2, w.2))
  rep := fun w c =>
    match c with
    | .setup => setupA W S cA r₀ h w.1
    | .prove xs => proveStepA W cA r₀ h w xs

/-- The game's simulators: the test's and the link's at every number; the session's on the table
number e is that for the number of the copy at the place e - 1 of the key's list. -/
def simsG (Sm : Sims L) : Hiop.Seeded.SimsG L :=
  ⟨fun _ => Sm.T, fun _ => Sm.Lk, fun e => Sm.B (h.nm (e - 1))⟩

/-- The game's bounds: M + 1 further tables; one test, on the first table; one link for each copy;
s1 sessions on each copy; no single read; one slot. -/
def boundsW (s1 : ℕ) : Hiop.BoundsR :=
  ⟨h.M + 1, fun e => if e = 0 then 1 else 0, fun e => if e = 0 then 0 else 1,
    fun e => if e = 0 then 0 else s1, fun _ => 0, 1⟩

/-- **THE SIMULATOR**: the reduction around the simulated game. -/
def simWholeKey (Sm : Sims L) (i₀ : I) (s1 : ℕ) (Gs : L.OutOfDomainSeed → Prop) (PP : Type) :
    ZKCP.Gen.Simulator (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) PP (FullKey lam L aT aL) X (RequestProof lam L) :=
  letI : Inhabited (FullKey lam L aT aL) := ⟨⟨default, r₀, none, []⟩⟩
  letI : Inhabited (RequestProof lam L) := ⟨⟨0, 0, none⟩⟩
  Compile.GlueB.simOf PP
    ((wrapW W S cA r₀ h).world
      (Hiop.Seeded.gameSim L (kitW W r₀ h) (simsG h Sm) i₀ (boundsW h s1) Gs _))
    ((Table.empty _, none), (none, Table.empty _))

end OnBytes.WholeKey
