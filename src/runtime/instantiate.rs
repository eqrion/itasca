//! Execute compiler-produced initialization code through the ordinary interpreter.
use super::platform::Alloc;
use super::*;

pub(crate) fn eval_const_exec<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    instance: usize,
    function: usize,
    ty: ValueType,
) -> Result<Value, ExecError> {
    let (lo, hi) = interp::synthetic::<M, P, F, A>(store, platform, instance, function)?;
    Ok(value::decode(ty, lo, hi, store.id))
}

pub(crate) fn initialize_segments<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    instance: usize,
) -> Result<(), ExecError> {
    let function = store.instances[instance].module.initialization;
    interp::synthetic::<M, P, F, A>(store, platform, instance, function)?;
    Ok(())
}
