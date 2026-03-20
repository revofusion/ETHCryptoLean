import Lake
open Lake DSL

package «ETHCryptoLean» where
  moreLeanArgs := #["-DautoImplicit=false"]

@[default_target]
lean_lib «ETHCryptoLean»

lean_lib «Test»
