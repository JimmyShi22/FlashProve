-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainDefs.lean: FROM THE BLOCKS' decide TO A ONE-CHAIN FILE's DECISION ON A
VIEW: the few names that the laws are stated with. Definitions alone; no theorem is stated.

  Served L ws     every column that is wanted (key, position, width) is there at its key and
                  position, with that width
  Walks ft L      the blocks' decisions in a row: each block's decide says ok on its own stretch of
                  the rounds, without the sealed digests, at ITS DECLARED GROUPS READ BY KEY
                  (readG, Johnson/Desc/Plain/OneYes.lean); nothing is left of the rounds
  IsOf2           a round's data of the protocol with several trees a round are a declared round's:
                  entry, items, and the kind of the entry's name
  wantTie1, wantTie   A CLOSED TEST, WITH CODE (one round's share; the whole), on (the stored
                  strings' depth, the rounds' data, the external openings, the declared rounds):
                  round by round the external openings are
                  the declared stored parts, and the opened trees the declared ones, at the shapes
                  that the rounds' data state
  lookV           a column of the view's, by key and position: in the two stored strings, or among
                  the strategy's own columns (colOf, Johnson/Prover/Link/LinkFrame.lean)

Nothing on soundness; nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkFrame
import Johnson.Desc.Plain.OneYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (readG lookY)
open _root_.Run.PQ (XO SgX xsAt)
open TypedOracleCompiler.Run.PQ (RD treeSh)
open _root_.Iop (twoExternalStrings)

variable {S Cl : Type}

/-- Every wanted column is there, with its width. -/
def Served (L : ℕ → ℕ → Option (List UInt64)) (ws : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ w ∈ ws, ∃ c, L w.1 w.2.1 = some c ∧ c.length = w.2.2

/-- **The blocks' decisions in a row**, each at its declared groups read by key. -/
def Walks (ft : ℕ) (L : ℕ → ℕ → Option (List UInt64)) :
    List (Block S Cl) → S → List Fmt.RoundView → S → Prop
  | [], s, rs, e => rs = [] ∧ e = s
  | b :: l, s, rs, e =>
    ∃ s', b.decide s ((rs.take b.rounds.length).map noDigest)
        ((groupsOf ft b.rounds ((rs.take b.rounds.length).map (·.drawn))).map (readG L)) = .ok s' ∧
      Walks ft L l s' (rs.drop b.rounds.length) e

/-- A round's data are a declared round's. -/
def IsOf2 (d : Fmt.DeclaredRound) (w : RD) : Prop :=
  w.entry = d.entry ∧ w.items = d.items ∧ Fmt.kindOf d.entry.name = some w.kind

/-- One round's share of the closed test. -/
def wantTie1 (a : ℕ) (all : List RD) (xs : List XO) (i : ℕ) (w : RD) (d : Fmt.DeclaredRound) : Bool :=
  ((xsAt xs i).map fun o => (o.which, o.from_, o.count)) ==
      d.stored.map (fun s => (s.item == 1, s.lo, s.count)) &&
    d.stored.all (fun s => s.sh.a == a && decide (s.item < 2)) &&
    w.opens == d.opens.map (·.1.tree) &&
    d.opens.all fun o => (treeSh all o.1.tree).map (·.a) == some o.1.a

/-- **The closed test.** -/
def wantTie (a : ℕ) (ds : List RD) (xs : List XO) (decls : List Fmt.DeclaredRound) : Bool :=
  ds.length == decls.length &&
    ((ds.zip decls).zipIdx.all fun r => wantTie1 a ds xs r.2 r.1.1 r.1.2)

/-- A column of the view's, by key and position. -/
def lookV (ds : List RD) (a : ℕ) (next : ℕ → List Fmt.Drawn → MsgV)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn) : ℕ → ℕ → Option (List UInt64) :=
  lookY a y (colOf ds 0 [] next Ds)

end Johnson.Prover.Link
