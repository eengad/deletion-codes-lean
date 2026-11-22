import Lean.Parser.Module

open Lean

/-- Check the explicit imports recognized by Lean's own module-header parser. -/
private def checkImports (path : String) (extra : List Name := []) : IO Unit := do
  let source ← IO.FS.readFile path
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
  if messages.hasErrors then
    for message in messages.toList do
      IO.eprintln (← message.toString)
    throw <| IO.userError s!"Invalid header in {path}"
  let `(Parser.Module.header| $[module%$_]? $[prelude%$_]? $imports*) := header
    | throw <| IO.userError s!"Could not read the header of {path}"
  let mut names := #[]
  for imp in imports do
    let `(Parser.Module.import| $[public%$_]? $[meta%$_]? import $[all%$_]? $mod) := imp
      | throw <| IO.userError s!"Could not read an import in {path}"
    let name := mod.getId
    unless Name.isPrefixOf `Mathlib name || extra.contains name do
      throw <| IO.userError s!"{path}: disallowed import {name}"
    names := names.push (toString name)
  IO.println s!"{path}: {String.intercalate ", " names.toList}"

def main : IO Unit := do
  checkImports "DeletionCode/Burst/Channel.lean"
  checkImports "DeletionCode/Explicit/Statement.lean" [`DeletionCode.Burst.Channel]
