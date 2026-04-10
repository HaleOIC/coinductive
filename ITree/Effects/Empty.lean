import ITree.Effect
import ITree.Definition
import ITree.Eval
import ITree.Exec

namespace ITree.Effects

def emptyE : Effect.{u} where
  I := PEmpty.{u+1}
  O := nofun
