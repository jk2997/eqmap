/*!

  Support for nl-compiler

*/

use crate::asic::CellLang;
use crate::driver::CircuitLang;
use crate::lut::LutLang;
use crate::verilog::PrimitiveType;
use bitvec::prelude::*;
use egg::{Id, RecExpr, Symbol};
use nl_compiler::FromId;
use safety_net::{
    Analysis, DrivenNet, Error, Identifier, Instantiable, Logic, Net, Netlist, Parameter,
    format_id, iter::DFSIterator,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::str::FromStr;

/// Trait for circuit elements that can provide a logic function
pub trait LogicFunc<L: CircuitLang> {
    /// Get the logic function/variant associated with the output at position `ind`.
    /// The children IDs are invalid/nulled in the returned [CircuitLang].
    fn get_logic_func(&self, ind: usize) -> Option<L>;
}

/// Helper trait for adding an LUT program node to a RecExpr<L>
pub trait AddProgram<L: CircuitLang> {
    /// Add a LUT program node to a RecExpr; returns None for CellLang
    fn add_program(&self, recexpr: &mut RecExpr<L>, program_value: u64) -> Option<Id>;
}

/// Maps a circuit element to its expression, root, and leaf mappings
#[derive(Debug, Clone)]
pub struct LogicMapping<L: CircuitLang, I: Instantiable + LogicFunc<L>> {
    expr: RecExpr<L>,
    roots: Vec<DrivenNet<I>>,
    leaves: HashMap<Symbol, DrivenNet<I>>,
    leaves_by_id: HashMap<Id, DrivenNet<I>>,
}

impl<L: CircuitLang, I: Instantiable + LogicFunc<L>> LogicMapping<L, I> {
    /// Get the expression
    pub fn get_expr(&self) -> RecExpr<L> {
        self.expr.clone()
    }

    /// Returns true if multiple nets are mapped
    pub fn is_multi_mapping(&self) -> bool {
        self.roots.len() > 1
    }

    /// Returns the circuit nodes at the root of this expression
    pub fn root_nets(&self) -> impl Iterator<Item = DrivenNet<I>> {
        self.roots.clone().into_iter()
    }

    /// Returns the Ids of the roots of the expression
    pub fn root_ids(&self) -> impl Iterator<Item = Id> {
        let last = self.expr.last().unwrap();
        if last.is_bus() {
            last.children().to_vec().into_iter()
        } else {
            let id: Id = (self.expr.len() - 1).into();
            let id = vec![id];
            id.into_iter()
        }
    }

    /// Returns the driven net associated with the variable leaf called `sym`
    pub fn get_leaf(&self, sym: &Symbol) -> Option<DrivenNet<I>> {
        self.leaves.get(sym).cloned()
    }

    /// Returns the driven net associated with the variable leaf with id `id` in the expressions
    pub fn get_leaf_by_id(&self, id: &Id) -> Option<DrivenNet<I>> {
        self.leaves_by_id.get(id).cloned()
    }

    /// Replaces the expression with a rewritten one
    ///
    /// # Panics
    /// Panics if the new expression does not have the same number of roots as the old one
    pub fn with_expr(self, expr: RecExpr<L>) -> Self {
        if self.expr.last().unwrap().is_bus() != expr.last().unwrap().is_bus() {
            panic!("New expression must have the same number of roots as the old one");
        }

        let mut leaves_by_id = HashMap::new();
        for (i, n) in expr.iter().enumerate() {
            if let Some(sym) = n.get_var() {
                let id: Id = i.into();
                leaves_by_id.insert(id, self.leaves[&sym].clone());
            }
        }

        Self {
            expr,
            leaves_by_id,
            ..self
        }
    }
}

/// Extracts the logic equation from a portion of a netlist.
pub struct LogicMapper<'a, L: CircuitLang, I: Instantiable + LogicFunc<L> + AddProgram<L>> {
    _netlist: &'a Netlist<I>,
    mappings: Vec<LogicMapping<L, I>>,
}

impl<'a, L, I> Analysis<'a, I> for LogicMapper<'a, L, I>
where
    L: CircuitLang + 'a,
    I: Instantiable + LogicFunc<L> + AddProgram<L> + 'a,
{
    fn build(netlist: &'a Netlist<I>) -> Result<Self, Error> {
        Ok(Self {
            _netlist: netlist,
            mappings: Vec::new(),
        })
    }
}

impl<'a, L: CircuitLang, I: Instantiable + LogicFunc<L> + AddProgram<L>> LogicMapper<'a, L, I> {
    /// Add a mapping for a specific net
    pub fn insert(&mut self, nets: Vec<DrivenNet<I>>) -> Result<RecExpr<L>, String> {
        let mut expr = RecExpr::<L>::default();
        let mut mapping: HashMap<DrivenNet<I>, Id> = HashMap::new();
        let mut leaves: HashMap<Symbol, DrivenNet<I>> = HashMap::new();
        let mut leaves_by_id: HashMap<Id, DrivenNet<I>> = HashMap::new();

        let roots = nets.clone();
        let mut nets = nets;
        let mut topo = Vec::new();
        let mut sorted = HashSet::new();

        while let Some(net) = nets.pop() {
            if sorted.contains(&net) {
                continue;
            }

            if net.is_an_input() {
                sorted.insert(net.clone());
                topo.push(net);
                continue;
            }

            let mut dfs = DFSIterator::new(self._netlist, net.clone().unwrap());
            let mut rdy = true;
            dfs.next(); // Skip the root node
            while let Some(n) = dfs.next() {
                if dfs.check_cycles() {
                    return Err("Cycle detected in netlist".to_string());
                }
                if n.is_multi_output() {
                    // TODO(matth2k): safety-net should have dfs by [DrivenNet]
                    return Err("Cannot map multi-output cells".to_string());
                }

                let n = n.get_output(0);
                if !sorted.contains(&n) {
                    rdy = false;
                    nets.push(net.clone());
                    nets.push(n);
                    break;
                }
            }

            if rdy {
                sorted.insert(net.clone());
                topo.push(net);
            }
        }

        for n in topo {
            if mapping.contains_key(&n) {
                continue;
            } else if let Some(inst_type) = n.get_instance_type()
                && let Some(mut logic) = inst_type.get_logic_func(n.get_output_index().unwrap())
            {
                let instant: &I = &*inst_type;
                if let Some(init_param) = instant.get_parameter(&"INIT".into())
                    && (!instant.is_seq())
                {
                    if let Parameter::BitVec(bv) = init_param {
                        let program_value: u64 = bv.load_le();
                        if let Some(program_id) = inst_type.add_program(&mut expr, program_value) {
                            logic.children_mut()[0] = program_id;
                        }
                    }
                    for (i, c) in n.clone().unwrap().inputs().enumerate() {
                        let cid = c
                            .get_driver()
                            .ok_or(format!("Failed to get driver for input {} of net {}", i, n))?;
                        let cid = mapping[&cid];
                        logic.children_mut()[i + 1] = cid;
                    }
                } else {
                    for (i, c) in n.clone().unwrap().inputs().enumerate() {
                        let cid = c
                            .get_driver()
                            .ok_or(format!("Failed to get driver for input {} of net {}", i, n))?;
                        let cid = mapping[&cid];
                        logic.children_mut()[i] = cid;
                    }
                }
                let id = expr.add(logic);
                mapping.insert(n.clone(), id);
            } else {
                let sym = n.get_identifier();
                let id = expr.add(L::var(sym.to_string().into()));
                mapping.insert(n.clone(), id);
                leaves.insert(sym.to_string().into(), n.clone());
                leaves_by_id.insert(id, n.clone());
            }
        }

        if roots.len() > 1 {
            let bus = L::bus(roots.iter().map(|n| mapping[n]));
            expr.add(bus);
        }

        self.mappings.push(LogicMapping {
            expr: expr.clone(),
            roots,
            leaves,
            leaves_by_id,
        });
        Ok(expr)
    }

    /// Add a mapping for a specific net
    pub fn insert_single_net(&mut self, net: DrivenNet<I>) -> Result<RecExpr<L>, String> {
        if net.is_an_input() {
            return Err("Inputs have trivial mappings".to_string());
        }

        self.insert(vec![net])
    }

    /// Get the mapped expressions
    pub fn mappings(self) -> Vec<LogicMapping<L, I>> {
        self.mappings
    }
}

/// Create an instantiable cell out of the [PrimitiveType]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimitiveCell {
    name: Identifier,
    ptype: PrimitiveType,
    inputs: Vec<Net>,
    outputs: Vec<Net>,
    params: HashMap<Identifier, Parameter>,
}

impl PrimitiveCell {
    /// Create a new primitive cell
    pub fn new(ptype: PrimitiveType, size: Option<usize>) -> Self {
        Self {
            name: if let Some(s) = size {
                format_id!("{}_X{}", ptype, s)
            } else {
                format_id!("{}", ptype)
            },
            ptype,
            inputs: ptype
                .get_input_list()
                .into_iter()
                .map(|s| Net::new_logic(Identifier::new(s)))
                .collect(),
            outputs: vec![Net::new_logic(Identifier::new(ptype.get_output()))],
            params: HashMap::new(),
        }
    }
}

impl Instantiable for PrimitiveCell {
    fn get_name(&self) -> &Identifier {
        &self.name
    }

    fn get_input_ports(&self) -> impl IntoIterator<Item = &Net> {
        self.inputs.iter()
    }

    fn get_output_ports(&self) -> impl IntoIterator<Item = &Net> {
        self.outputs.iter()
    }

    fn has_parameter(&self, id: &Identifier) -> bool {
        self.params.contains_key(id)
    }

    fn get_parameter(&self, id: &Identifier) -> Option<Parameter> {
        self.params.get(id).cloned()
    }

    fn set_parameter(&mut self, id: &Identifier, val: Parameter) -> Option<Parameter> {
        self.params.insert(id.clone(), val)
    }

    fn parameters(&self) -> impl Iterator<Item = (Identifier, Parameter)> {
        self.params.clone().into_iter()
        // std::iter::empty()
    }

    fn from_constant(val: Logic) -> Option<Self> {
        match val {
            Logic::False => Some(PrimitiveCell::new(PrimitiveType::GND, None)),
            Logic::True => Some(PrimitiveCell::new(PrimitiveType::VCC, None)),
            _ => None,
        }
    }

    fn get_constant(&self) -> Option<Logic> {
        match self.ptype {
            PrimitiveType::GND => Some(Logic::False),
            PrimitiveType::VCC => Some(Logic::True),
            _ => None,
        }
    }

    fn is_seq(&self) -> bool {
        self.ptype.is_reg()
    }
}

impl LogicFunc<CellLang> for PrimitiveCell {
    fn get_logic_func(&self, _ind: usize) -> Option<CellLang> {
        match self.ptype {
            PrimitiveType::AND => Some(CellLang::And([0.into(); 2])),
            PrimitiveType::VCC => Some(CellLang::Const(true)),
            PrimitiveType::GND => Some(CellLang::Const(false)),
            PrimitiveType::OR => Some(CellLang::Or([0.into(); 2])),
            PrimitiveType::NOT => Some(CellLang::Inv([0.into()])),
            _ if self.ptype.is_lut() => None,
            _ => Some(CellLang::Cell(
                self.ptype.to_string().into(),
                vec![0.into(); self.ptype.get_num_inputs()],
            )),
        }
    }
}

impl LogicFunc<LutLang> for PrimitiveCell {
    fn get_logic_func(&self, _ind: usize) -> Option<LutLang> {
        match self.ptype {
            PrimitiveType::AND => Some(LutLang::And([0.into(); 2])),
            PrimitiveType::VCC => Some(LutLang::Const(Logic::True)),
            PrimitiveType::GND => Some(LutLang::Const(Logic::False)),
            PrimitiveType::NOR => Some(LutLang::Nor([0.into(); 2])),
            PrimitiveType::XOR => Some(LutLang::Xor([0.into(); 2])),
            PrimitiveType::MUX => Some(LutLang::Mux([0.into(); 3])),
            PrimitiveType::NOT => Some(LutLang::Not([0.into()])),
            PrimitiveType::FDRE => Some(LutLang::Reg([0.into(); 4])),
            _ if self.ptype.is_lut() => Some(LutLang::Lut(
                vec![0.into(); self.ptype.get_num_inputs() + 1].into(),
            )),
            _ => None,
        }
    }
}

impl AddProgram<LutLang> for PrimitiveCell {
    fn add_program(&self, recexpr: &mut RecExpr<LutLang>, program_value: u64) -> Option<Id> {
        Some(recexpr.add(LutLang::Program(program_value)))
    }
}

impl AddProgram<CellLang> for PrimitiveCell {
    fn add_program(&self, _recexpr: &mut RecExpr<CellLang>, _program_value: u64) -> Option<Id> {
        None
    }
}

/// Trait to create instantiable cell from the logic node
pub trait LogicCell<I: Instantiable> {
    /// Returns the instantiable cell type associated with this logic node
    fn get_cell(&self) -> Option<I>;
}

impl<I: Instantiable + LogicFunc<L>, L: CircuitLang + LogicCell<I>> LogicMapping<L, I> {
    /// Rewrite the expression into the netlist
    pub fn rewrite(self, netlist: &Rc<Netlist<I>>) -> Result<Vec<DrivenNet<I>>, Error> {
        let mut mapping: HashMap<Id, DrivenNet<I>> = HashMap::new();
        let mut lut_init: u64 = 0;
        for (i, n) in self.expr.iter().enumerate() {
            if let Some(var) = n.get_var() {
                mapping.insert(i.into(), self.leaves[&var].clone());
            } else if let Some(program_val) = n.extract_program() {
                lut_init = program_val;
            } else if !n.is_bus() {
                let mut cell = n.get_cell().ok_or(Error::ParseError(format!(
                    "Cannot reinsert node {} without associated cell",
                    n
                )))?;
                let cell_name = cell.get_name().to_string();
                let mut operands: Vec<DrivenNet<I>> = vec![];
                if cell_name.contains("LUT") {
                    let lut_k_char = cell_name.as_bytes()[3] as char;
                    let lut_k = lut_k_char.to_digit(10).unwrap() as usize;
                    cell.set_parameter(&"INIT".into(), Parameter::bitvec(1 << lut_k, lut_init));
                    operands = n
                        .children()
                        .iter()
                        .skip(1)
                        .map(|c| mapping[c].clone())
                        .collect::<Vec<_>>();
                } else {
                    if cell_name.contains("FDRE") {
                        cell.set_parameter(&"INIT".into(), Parameter::Logic(Logic::X));
                    }
                    operands = n
                        .children()
                        .iter()
                        .map(|c| mapping[c].clone())
                        .collect::<Vec<_>>();
                }
                let inst_name = format_id!("reinst_{}", i);
                let instance = netlist.insert_gate(cell, inst_name, &operands)?;
                // TODO(matth2k): Support multi-output cells
                assert!(!instance.is_multi_output());
                let out = instance.get_output(0);
                mapping.insert(i.into(), out);
            }
        }

        let new_roots: Vec<_> = self.root_ids().map(|id| mapping[&id].clone()).collect();
        let old_net_names = self
            .root_nets()
            .map(|n| n.as_net().clone())
            .collect::<Vec<_>>();

        let old_roots: Vec<_> = self.root_nets().collect();

        drop(self);
        drop(mapping);

        for (old, new) in old_roots.into_iter().zip(new_roots.iter()) {
            if old.is_top_level_output() {
                let id = old.get_identifier() + "_old".into();
                old.as_net_mut().set_identifier(id);
            }

            netlist.replace_net_uses(old, new)?;
        }
        netlist.clean()?;

        for (new, n) in new_roots.iter().zip(old_net_names.into_iter()) {
            *new.as_net_mut() = n;
        }

        Ok(new_roots)
    }
}

impl LogicCell<PrimitiveCell> for CellLang {
    fn get_cell(&self) -> Option<PrimitiveCell> {
        match self {
            CellLang::And(_) => Some(PrimitiveCell::new(PrimitiveType::AND2, Some(1))),
            CellLang::Or(_) => Some(PrimitiveCell::new(PrimitiveType::OR2, Some(1))),
            CellLang::Inv(_) => Some(PrimitiveCell::new(PrimitiveType::INV, Some(1))),
            CellLang::Const(b) => PrimitiveCell::from_constant(Logic::from(*b)),
            CellLang::Cell(name, _) => match PrimitiveType::from_str(name.as_str()) {
                Ok(ptype) => Some(PrimitiveCell::new(ptype, Some(1))),
                Err(_) => None,
            },
            _ => None,
        }
    }
}

impl LogicCell<PrimitiveCell> for LutLang {
    fn get_cell(&self) -> Option<PrimitiveCell> {
        match self {
            LutLang::And(_) => Some(PrimitiveCell::new(PrimitiveType::AND, None)),
            LutLang::Mux(_) => Some(PrimitiveCell::new(PrimitiveType::MUX, None)),
            LutLang::Nor(_) => Some(PrimitiveCell::new(PrimitiveType::NOR, None)),
            LutLang::Not(_) => Some(PrimitiveCell::new(PrimitiveType::NOT, None)),
            LutLang::Const(b) => PrimitiveCell::from_constant(*b),
            //       LutLang::DC => PrimitiveCell::from_constant(Logic::X),
            LutLang::Reg(_) => Some(PrimitiveCell::new(PrimitiveType::FDRE, None)),
            LutLang::Xor(_) => Some(PrimitiveCell::new(PrimitiveType::XOR, None)),
            LutLang::Lut(l) => match l.len() {
                2 => Some(PrimitiveCell::new(PrimitiveType::LUT1, None)),
                3 => Some(PrimitiveCell::new(PrimitiveType::LUT2, None)),
                4 => Some(PrimitiveCell::new(PrimitiveType::LUT3, None)),
                5 => Some(PrimitiveCell::new(PrimitiveType::LUT4, None)),
                6 => Some(PrimitiveCell::new(PrimitiveType::LUT5, None)),
                7 => Some(PrimitiveCell::new(PrimitiveType::LUT6, None)),
                _ => None,
            },
            _ => None,
        }
    }
}

impl FromId for PrimitiveCell {
    fn from_id(s: &Identifier) -> Result<Self, Error> {
        match PrimitiveType::from_str(&s.to_string()) {
            Ok(ptype) => Ok(PrimitiveCell::new(
                ptype, None, /* Drop the size for logic synthesis */
            )),
            Err(e) => Err(Error::ParseError(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    fn and_gate() -> PrimitiveCell {
        PrimitiveCell::new(PrimitiveType::AND, None)
    }

    fn reg_cell() -> PrimitiveCell {
        PrimitiveCell::new(PrimitiveType::FDRE, None)
    }

    fn and_netlist() -> Rc<Netlist<PrimitiveCell>> {
        let netlist = Netlist::new("example".to_string());

        // Add the the two inputs
        let a = netlist.insert_input("a".into());
        let b = netlist.insert_input("b".into());

        // Instantiate an AND gate
        let instance = netlist
            .insert_gate(and_gate(), "inst_0".into(), &[a, b])
            .unwrap();

        // Make this AND gate an output
        // Setting both the net and output name to "y" tests more edge cases
        instance
            .get_output(0)
            .as_net_mut()
            .set_identifier("y".into());
        instance.expose_with_name("y".into());

        netlist
    }

    fn divider_netlist() -> Rc<Netlist<PrimitiveCell>> {
        let netlist = Netlist::new("example".to_string());

        // Add the the input
        let a = netlist.insert_input("a".into());

        // Instantiate a reg
        let reg = netlist.insert_gate_disconnected(reg_cell(), "inst_0".into());

        // And last val and input
        let and = netlist
            .insert_gate(and_gate(), "inst_1".into(), &[a, reg.get_output(0)])
            .unwrap();

        reg.find_input(&"D".into()).unwrap().connect(and.into());

        // Make this Reg an output
        reg.expose_with_name("y".into());

        netlist
    }

    fn and_const_netlist() -> Rc<Netlist<PrimitiveCell>> {
        let netlist = Netlist::new("example".to_string());

        // Add the the two inputs
        let a = netlist.insert_constant(Logic::True, "a".into()).unwrap();
        let b = netlist.insert_constant(Logic::False, "a".into()).unwrap();

        // Instantiate an AND gate
        let instance = netlist
            .insert_gate(and_gate(), "inst_0".into(), &[a, b])
            .unwrap();

        // Make this AND gate an output
        instance.expose_with_name("y".into());

        netlist
    }

    #[test]
    fn test_and_gate() {
        let netlist = and_netlist();
        let output = netlist.last().unwrap().get_output(0);

        let mapper = netlist.get_analysis::<'_, LogicMapper<'_, CellLang, _>>();
        assert!(mapper.is_ok());
        let mut mapper = mapper.unwrap();

        // Check the RecExpr is correct
        let expr = mapper.insert_single_net(output.clone());
        assert!(expr.is_ok());
        let expr = expr.unwrap();
        assert_eq!(expr.to_string(), "(AND a b)");

        // Check the root properties are correct
        let mut mapping = mapper.mappings();
        assert!(!mapping.is_empty());
        let mapping = mapping.pop().unwrap();
        assert_eq!(mapping.root_nets().next().unwrap(), output);
        assert_eq!(netlist.objects().count(), mapping.get_expr().as_ref().len());

        // Check the leaves
        let l0 = mapping.get_leaf(&"a".into());
        assert!(l0.is_some());
        let l0 = l0.unwrap();
        assert_eq!(l0, netlist.first().unwrap().into());
    }

    #[test]
    fn test_consts() {
        let netlist = and_const_netlist();
        let output = netlist.last().unwrap().get_output(0);

        let mapper = netlist.get_analysis::<'_, LogicMapper<'_, CellLang, _>>();
        assert!(mapper.is_ok());
        let mut mapper = mapper.unwrap();

        // Check the RecExpr is correct
        let expr = mapper.insert_single_net(output.clone());
        assert!(expr.is_ok());
        let expr = expr.unwrap();
        assert_eq!(expr.to_string(), "(AND true false)");
    }

    #[test]
    fn test_divider() {
        let netlist = divider_netlist();
        let output = netlist.last().unwrap().get_output(0);

        let mapper = netlist.get_analysis::<'_, LogicMapper<'_, CellLang, _>>();
        assert!(mapper.is_ok());
        let mut mapper = mapper.unwrap();

        let mapping = mapper.insert_single_net(output);
        assert!(mapping.is_err());

        let err = mapping.unwrap_err();
        // TODO(matth2k): Eventually simple cycles should be supported by breaking them up
        assert!(err.contains("Cycle"));
    }

    #[test]
    fn test_and_flip() {
        let netlist = and_netlist();
        let output = netlist.last().unwrap().get_output(0);

        let mapper = netlist.get_analysis::<'_, LogicMapper<'_, CellLang, _>>();
        assert!(mapper.is_ok());
        let mut mapper = mapper.unwrap();

        // Check the RecExpr is correct
        let _ = mapper.insert_single_net(output);

        let mut mapping = mapper.mappings();
        assert!(!mapping.is_empty());
        let mapping = mapping.pop().unwrap();

        let rewrite: RecExpr<CellLang> = "(AND b a)".parse().unwrap();
        let mapping = mapping.with_expr(rewrite);

        let rewrite = mapping.rewrite(&netlist);
        assert!(rewrite.is_ok());
        assert!(netlist.objects().count() == 3);
    }
}
