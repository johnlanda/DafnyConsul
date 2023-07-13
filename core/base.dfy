include "std.dfy"

module def.base {
    import opened std

    datatype Error =
        EntityDoesNotExist |
        TypeError
        // OR together additional datatypes as needed for errors

    type Result<T> = std.Result<T, Error>
    type UnitResult = Result<()>

    function Ok<T>(v: T): Result<T> {
        Result.Ok(v)
    }

    function Err<T>(v: Error): Result<T> {
        Result.Err(v)
    }

}