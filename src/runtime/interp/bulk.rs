//! Bulk operations share their bounds checks with segment initialization.
use super::*;
pub(super) fn execute<M: MemoryBuffer>(
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    slots: &[u64],
    instruction: Instr,
) -> Result<(), ExecError> {
    match instruction {
        Instr::DataDrop { data } => {
            let address = store.instances[inst].data[data as usize];
            store.datas[address].bytes = Vec::new();
        }
        Instr::ElemDrop { elem } => {
            let address = store.instances[inst].elements[elem as usize];
            store.elems[address].refs = Vec::new();
        }
        Instr::MemoryFill { d } | Instr::MemoryCopy { d } | Instr::MemoryInit { d, .. } => {
            let destination = slots[base + d as usize] as u32 as u64;
            let source = slots[base + d as usize + 1] as u32;
            let len = slots[base + d as usize + 2] as u32 as u64;
            let memory = store.instances[inst].memories[0].index;
            let bytes = store.memories[memory].buf.bytes().len();
            let dst = range(destination, len, bytes, Trap::MemoryOutOfBounds)?;
            match instruction {
                Instr::MemoryInit { data, .. } => {
                    let address = store.instances[inst].data[data as usize];
                    let data = &store.datas[address].bytes;
                    let src = range(source as u64, len, data.len(), Trap::MemoryOutOfBounds)?;
                    let target = store.memories[memory].buf.bytes_mut();
                    target[dst].copy_from_slice(&data[src]);
                }
                Instr::MemoryCopy { .. } => {
                    let src = range(source as u64, len, bytes, Trap::MemoryOutOfBounds)?;
                    let target = store.memories[memory].buf.bytes_mut();
                    if dst.end <= src.start {
                        let (left, right) = target.split_at_mut(src.start);
                        left[dst].copy_from_slice(&right[..len as usize]);
                    } else if src.end <= dst.start {
                        let (left, right) = target.split_at_mut(dst.start);
                        right[..len as usize].copy_from_slice(&left[src]);
                    } else if dst.start <= src.start {
                        let mut i = 0;
                        while i < len as usize {
                            target[dst.start + i] = target[src.start + i];
                            i += 1;
                        }
                    } else {
                        let mut i = len as usize;
                        while i > 0 {
                            i -= 1;
                            target[dst.start + i] = target[src.start + i];
                        }
                    }
                }
                _ => {
                    let target = store.memories[memory].buf.bytes_mut();
                    target[dst].fill(source as u8);
                }
            }
        }
        Instr::TableCopy { d, entry } | Instr::TableInit { d, entry } => {
            let (a, b) = store.instances[inst].module.functions[function].indirect[entry as usize];
            let destination = slots[base + d as usize] as u32 as u64;
            let source = slots[base + d as usize + 1] as u32 as u64;
            let len = slots[base + d as usize + 2] as u32 as u64;
            let table_index = if matches!(instruction, Instr::TableInit { .. }) {
                b
            } else {
                a
            };
            let table = store.instances[inst].tables[table_index as usize].index;
            let dst = range(
                destination,
                len,
                store.tables[table].elements.len(),
                Trap::TableOutOfBounds,
            )?;
            if matches!(instruction, Instr::TableInit { .. }) {
                let src = range(
                    source,
                    len,
                    store.elems[store.instances[inst].elements[a as usize]]
                        .refs
                        .len(),
                    Trap::TableOutOfBounds,
                )?;
                let mut i = 0;
                while i < len as usize {
                    store.tables[table].elements[dst.start + i] =
                        store.elems[store.instances[inst].elements[a as usize]].refs[src.start + i];
                    i += 1;
                }
            } else {
                let src_table = store.instances[inst].tables[b as usize].index;
                let src = range(
                    source,
                    len,
                    store.tables[src_table].elements.len(),
                    Trap::TableOutOfBounds,
                )?;
                if table == src_table && dst.start > src.start {
                    let mut i = len as usize;
                    while i > 0 {
                        i -= 1;
                        store.tables[table].elements[dst.start + i] =
                            store.tables[src_table].elements[src.start + i];
                    }
                } else {
                    let mut i = 0;
                    while i < len as usize {
                        store.tables[table].elements[dst.start + i] =
                            store.tables[src_table].elements[src.start + i];
                        i += 1;
                    }
                }
            }
        }
        Instr::TableFill { d, table } => {
            let destination = slots[base + d as usize] as u32 as u64;
            let value = slots[base + d as usize + 1];
            let len = slots[base + d as usize + 2] as u32 as u64;
            let t = store.instances[inst].tables[table as usize].index;
            let dst = range(
                destination,
                len,
                store.tables[t].elements.len(),
                Trap::TableOutOfBounds,
            )?;
            let mut i = dst.start;
            while i < dst.end {
                store.tables[t].elements[i] = value;
                i += 1;
            }
        }
        _ => return Err(ExecError::BadArguments),
    }
    Ok(())
}
