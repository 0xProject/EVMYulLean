import EvmYul.Yul.State

namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments                              : Exception
  | NotEncodableRLP                               : Exception
  | InvalidInstruction                            : Exception
  | OutOfFuel                                     : Exception
  | StaticModeViolation                           : Exception
  | MissingContract (s : String)                  : Exception
  | MissingContractFunction (s : String)          : Exception
  | InvalidExpression                             : Exception
  | YulEXTCODESIZENotImplemented                  : Exception
  /-- `REVERT` (EIP-140), with the bytes it returns: `memory[offset, offset + size)`. -/
  | Revert (data : ByteArray)                     : Exception
  | YulHalt (state : Yul.State) (value : UInt256) : Exception
  /-- `RETURNDATACOPY` read past the end of the return-data buffer (EIP-211):
  an exceptional halt, as in the EVM semantics. -/
  | InvalidMemoryAccess                           : Exception
  -- | StopInvoked        : Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .InvalidArguments => "InvalidArguments"
      | .NotEncodableRLP => "NotEncodableRLP"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfFuel => "OutOfFuel"
      | .StaticModeViolation => "StaticModeViolation"
      | .MissingContract s => "MissingContract: " ++ s
      | .MissingContractFunction f => "MissingContractFunction: " ++ f
      | .InvalidExpression => "InvalidExpression"
      | .YulEXTCODESIZENotImplemented => "YulEXTCODESIZENotImplemented"
      | .Revert _ => "Revert"
      | .YulHalt _ _ => "YulHalt: (holds a state and a value)"
      | .InvalidMemoryAccess => "InvalidMemoryAccess"


end Yul

end EvmYul
