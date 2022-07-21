from __future__ import annotations
from abc import abstractmethod
import sys
from typing import Set
from pymjc.back import assem, flowgraph, graph
from pymjc.front import frame, temp


class RegAlloc (temp.TempMap):
    def __init__(self, frame: frame.Frame, instr_list: assem.InstrList):
        
        self.frame: frame.Frame = frame
        self.instrs: assem.InstrList = instr_list
        
        self.assemFlowGraph = None
        self.liveness = None

        self.worklistMoveNodes: set[graph.Node] = {}
        self.spillTemps: set[temp.Temp] = {}
        
        # procedimento principal
        shallContinue = True
        while (shallContinue):

            self.LiveAnalysis() #Como no livro
            self.Init(); # Método auxiliar para inicializar todas as nossas propriedades adequadamente
            self.Build(); # Como no livro
            self.MakeWorklist(); # Como no livro
    

    def LiveAnalysis(self) -> None:
        self.assemFlowGraph = flowgraph.AssemFlowGraph(self.instrs)
        self.liveness = Liveness(self.assemFlowGraph)

    def Init(self) -> None:

        # Nós gerais
        self.pre_colored_nodes = []
        self.normal_colored_nodes = {}

        # Nós separados por etapas
        self.initial_nodes = []
        self.spill_nodes = {}
        self.coalesce_nodes = {}

        # Pilha de nós para coloração
        self.node_stack = []

        # WorkLists
        self.simplify_worklist = {}
        self.freeze_worklist = {}
        self.spill_worklist = {}

        # Nós move
        self.coalesce_move_nodes = {}
        self.constrain_move_nodes = {}
        self.freeze_move_nodes = {}
        self.active_move_nodes = {}

        # Para decidir se vai ter um custo personalizado de spill
        self.spill_cost = {}

        # Propriedades referentes à adjacencia
        self.adjacence_sets = {}
        self.adjacence_list = {}

        # Moves
        self.move_nodes_list = {}

        # Tabelas de referência a características dos nós(alias, color e degree)
        self.node_alias_table = {}
        self.node_color_table = {}
        self.node_degree_table = {}

        # Vamos criar agora a lista de registradores para temporários pré-coloridos
        for counter in range(len(self.frame.registers())):
            
            inst_temp: temp.Temp = self.frame.registers()[counter]
            node: graph.Node = self.liveness_output.tnode(inst_temp)

            # Vamos adicionar o nó com o seu spill cost máximo
            self.pre_colored_nodes.append(node)
            self.spill_cost[node.to_string()] = sys.maxsize

            # Atualizaremos na tabela de cores e grau
            self.node_color_table[node.to_string()] = node
            self.node_degree_table[node.to_string()] = 0

        # Criando lista de registradores para temp não pré-coloridos
        node_list = self.liveness_output.nodes()
        while node_list != None:
            node: graph.Node = node_list.head

            if not node in self.pre_colored_nodes:
                self.initial_nodes.append(node)
                self.spill_cost[node.to_string()] = 1

                self.node_degree_table[node.to_string()] = 0
            
            node_list = node_list.tail
    
    # Responsável pela etapa de Build - pg 235
    def Build(self):
        
        self.nodeList = self.assemFlowGraph.nodes()
        
        # forall b ∈ blocks in program
        while (self.nodeList != None):
            node = self.nodeList.head
           
            # let live = liveOut(b)
            live: set[temp.Temp] = self.liveness.out(node).copy()
            

            if (self.assemFlowGraph.is_move(node)):
                
                uses: temp.TempList = self.assemFlowGraph.use(node)
                while (uses != None):
                    live.remove(uses.head)
                    uses = uses.tail

                # moveList[n] ∪ {I}
                uses = self.assemFlowGraph.use(node)
                while (uses != None):
                    moveNodeSet = self.color.getMoveNodeSet(self.liveness.tnode(uses.head))
                    moveNodeSet.add(node)
                    uses = uses.tail
                defs = self.assemFlowGraph.deff(node)
                while (defs != None):
                    moveNodeSet = self.color.getMoveNodeSet(self.liveness.tnode(defs.head))
                    moveNodeSet.add(node)
                    defs = defs.tail
               
                # worklistMoves ← worklistMoves ∪ {I}
                self.worklistMoveNodes.add(node)

            # live ← live ∪ def(I)
            defs = self.assemFlowGraph.deff(node)
            while (defs != None):
                live.add(defs.head)
                defs = defs.tail

            # forall d ∈ def(I)
            defs = self.assemFlowGraph.deff(node)
            while (defs != None):
                # forall l ∈ live
                for liveTemp in live:
                    # AddEdge AddEdge(l, d)
                    if (liveTemp!=defs.head):
                        self.color.addEdge(self.liveness.tnode(liveTemp), self.liveness.tnode(defs.head))
                defs = defs.tail
            self.nodeList = self.nodeList.tail
    
    def MakeWorklist():
        #TODO
        ...


    # Uma classe que vamos precisar internamente para não perdermos referência da head
    class MemHeadTailTemp:

        def __init__(self, instrList: assem.InstrList, temp: temp.Temp):
            # Manteremos referência da head, tail e de um temporário
            self.head = instrList
            self.temp = temp
            self.tail = self.head

            while (self.tail != None):
                if (self.tail.tail == None):
                    break
                self.tail = self.tail.tail

    # Gera uma instrução de Fetch
    def genFetch(self, access: frame.Access, temp: temp.Temp) -> RegAlloc.MemHeadTailTemp:
        # Adicionamos o temporário na lista de transbordo
        self.spillTemps.add(temp)
       
        # Instanciamos o Fetch de modo semelhante da etapa passada
        fetchInstr = self.tree.MOVE(self.tree.TEMP(temp), access.exp(self.tree.TEMP(self.frame.FP())))
       
        # Criamos a Head Tail que retornaremos
        return RegAlloc.MemHeadTailTemp(self.frame.codegen(self.canon.Canon.linearize(fetchInstr)), temp)
    
    def getStore(self, access: frame.Access, temp: temp.Temp) -> RegAlloc.MemHeadTailTemp:
        # Adicionamos o temporário na lista de transbordo
        self.spillTemps.add(temp)
        
        # Criamos a Head Tail que retornaremos
        s: self.tree.Stm = self.tree.MOVE(access.exp(self.tree.TEMP(self.frame.FP())), self.tree.TEMP(temp))
        return RegAlloc.MemHeadTailTemp(self.frame.codegen(self.canon.Canon.linearize(s)), temp)

    def rewriteProgram(self):
        accessTable: dict[temp.Temp, frame.Access] = {}

        # Nessa etapa, vamos erar os nós que transbordaram
        for node in self.color.spillNodes:
            accessTable[self.liveness.gtemp(node)] = frame.alloc_local(True)
       
        # Geramos duas listas de instruções
        insnsPast = self.instrs
        tailReference = self.instrs = None
       
        # Iterando sobre a insns antiga
        while (insnsPast != None):
            
            # Vamos atualizar os usos das instruções no caso de Fetch
            tempList = insnsPast.head.use()
            while (tempList != None):
                temp = tempList.head
                access = accessTable.get(temp)

                 # Se não houver acesso, é hora de transbordar
                if (access != None):

                    result = self.genFetch(access, temp)
                    
                    # Precisamos atualizar a cauda dependendo do insns
                    if (self.instrs != None):
                        tailReference.tail = result.head
                    else:
                        self.instrs = result.head

                    # Atualizamos novamente a cauda
                    tailReference = result.tail

                # Vamos colocar a nova instrução   
                newInstrList = assem.InstrList(insnsPast.head, None)

                # Precisamos atualizar a cauda dependendo do insns
                if (self.instrs != None):
                    tailReference = tailReference.tail = newInstrList
                else:
                    self.instrs = tail = newInstrList
                
                defTempList = insnsPast.head.deff()
                while (defTempList != None):
                    temp = defTempList.head
                    access = accessTable.get(temp)
                    if (access != None):
                        result = self.getStore(access, defTempList.head)
                        if (self.instrs != None):
                            tail.tail = result.head
                        else:
                            self.instrs = result.head
                        tail = result.tail
                        defTempList.head = result.temp
                    defTempList = defTempList.tail
                    
            insnsPast = insnsPast.tail

    # Método tempMap, para obtermos a String do temporário no map
    def temp_map(self, temp: temp.Temp) -> str:
        temp_str: str = self.frame.temp_map(temp)

        if (temp_str==None):
            temp_str = self.color.temp_map(temp)
        
        return temp_str
    

class Color(temp.TempMap):
    def __init__(self, ig: InterferenceGraph, initial: temp.TempMap, registers: temp.TempList):
        #TODO
        pass
    
    def spills(self) -> temp.TempList:
        #TODO
        return None

    def temp_map(self, temp: temp.Temp) -> str:
        #TODO
        return temp.to_string()

class InterferenceGraph(graph.Graph):
    
    @abstractmethod
    def tnode(self, temp:temp.Temp) -> graph.Node:
        pass

    @abstractmethod
    def gtemp(self, node: graph.Node) -> temp.Temp:
        pass

    @abstractmethod
    def moves(self) -> MoveList:
        pass
    
    def spill_cost(self, node: graph.Node) -> int:
      return 1


class Liveness (InterferenceGraph):

    def __init__(self, flow: flowgraph.FlowGraph):
        self.live_map = {}
        
        #Flow Graph
        self.flowgraph: flowgraph.FlowGraph = flow
        
        #IN, OUT, GEN, and KILL map tables
        #The table maps complies with: <Node, Set[Temp]> 
        self.in_node_table   = {}
        self.out_node_table  = {}
        self.gen_node_table  = {}
        self.kill_node_table = {}

        #Util map tables
        #<Node, Temp>
        self.rev_node_table = {}
        #<Temp, Node>
        self.map_node_table = {}
        
        #Move list
        self.move_list: MoveList = None

        self.build_gen_and_kill()
        self.build_in_and_out()
        self.build_interference_graph()
    
    def add_ndge(self, source_node: graph.Node, destiny_node: graph.Node):
        if (source_node is not destiny_node and not destiny_node.comes_from(source_node) and not source_node.comes_from(destiny_node)):
            super.add_edge(source_node, destiny_node)

    def show(self, out_path: str) -> None:
        if out_path is not None:
            sys.stdout = open(out_path, 'w')   
        node_list: graph.NodeList = self.nodes()
        while(node_list is not None):
            temp: temp.Temp = self.rev_node_table.get(node_list.head)
            print(temp + ": [ ")
            adjs: graph.NodeList = node_list.head.adj()
            while(adjs is not None):
                print(self.rev_node_table.get(adjs.head) + " ")
                adjs = adjs.tail

            print("]")
            node_list = node_list.tail
    
    def get_node(self, temp: temp.Temp) -> graph.Node:
      requested_node: graph.Node = self.map_node_table.get(temp)
      if (requested_node is None):
          requested_node = self.new_node()
          self.map_node_table[temp] = requested_node
          self.rev_node_table[requested_node] = temp

      return requested_node

    def node_handler(self, node: graph.Node):
        def_temp_list: temp.TempList = self.flowgraph.deff(node)
        while(def_temp_list is not None):
            got_node: graph.Node  = self.get_node(def_temp_list.head)

            for live_out in self.out_node_table.get(node):
                current_live_out = self.get_node(live_out)
                self.add_edge(got_node, current_live_out)

            def_temp_list = def_temp_list.tail

  
    def move_handler(self, node: graph.Node):
        source_node: graph.Node  = self.get_node(self.flowgraph.use(node).head)
        destiny_node: graph.Node = self.get_node(self.flowgraph.deff(node).head)

        self.move_list = MoveList(source_node, destiny_node, self.move_list)
    
        for temp in self.out_node_table.get(node):
            got_node: graph.Node = self.get_node(temp)
            if (got_node is not source_node ):
                self.addEdge(destiny_node, got_node)


    def out(self, node: graph.Node) -> Set[temp.Temp]:
        temp_set = self.out_node_table.get(node)
        return temp_set


    def tnode(self, temp:temp.Temp) -> graph.Node:
        node: graph.Node = self.map_node_table.get(temp)
        if (node is None ):
            node = self.new_node()
            self.map_node_table[temp] = node
            self.rev_node_table[node] = temp
        
        return node

    def gtemp(self, node: graph.Node) -> temp.Temp:
        temp: temp.Temp = self.rev_node_table.get(node)
        return temp

    def moves(self) -> MoveList:
        return self.move_list

    def temp_to_set(self, node: graph.Node) -> Set[int]:
        set_aux = set()
        for temp_element in self.out(node):
            set_aux.add(temp_element.number)

        return set_aux
    
    def build_gen_and_kill(self):
        #TODO
        pass

    def build_in_and_out(self):
        in_set_aux  = set()
        out_set_aux = set()
        
        in_set_stop = set()
        out_set_stop = set()

        nodes = self.flowgraph.nodes();

        while True:
            head = nodes.head 
            tail = nodes.tail

            while head is not None:
                in_set_aux  = self.in_node_table.get(head, set())
                out_set_aux = self.out_node_table.get(head, set())

                in_set_stop.union(self.in_node_table.get(head, set()))
                out_set_stop.union(self.in_node_table.get(head, set()))

                diff_set    = self.out(head) - self.flowgraph.deff(head).templist_to_set()
                union_set   = diff_set.union(self.flowgraph.use(head).templist_to_set())
                self.in_node_table[head] = union_set

                n_list = head.succ()
                iter_h = n_list.head
                iter_t = n_list.tail
                while iter_h is not None:
                    self.out_node_table.get(head, set()).union(self.in_node_table.get(iter_h, set())) 
                    iter_h = iter_t.head
                    iter_t = iter_t.tail

                head = tail.head
                tail = tail.tail
                
            if in_set_aux == in_set_stop and out_set_stop == out_set_aux:
                break
    
    def build_interference_graph(self):
        outs_node_table: dict[graph.Node, Set[graph.Node]] = {
            k: self.outs_set_to_node_set(v) for k, v in self.out_node_table.items()
        }

        nodes = self.flowgraph.nodes()

        while nodes.head is not None:
            deffs = self.flowgraph.deff(nodes.head)
            uses  = self.flowgraph.use(nodes.head)

            deffs_list = self.temp_to_list(deffs)
            uses_list  = self.temp_to_list(uses)

            for deff_node in deffs_list:
                live_outs_node = outs_node_table.get(deff_node, set())

                for out_node in live_outs_node:
                    is_move = self.flowgraph.is_move(deff_node)

                    if is_move and out_node not in uses_list:
                        self.add_ndge(deff_node, out_node)
                    
                    if not is_move:
                        self.add_ndge(deff_node, out_node)

            nodes = nodes.tail

    def outs_set_to_node_set(self, set_temp: Set[temp.Temp]) -> Set[graph.Node]:
        return { self.tnode(out) for out in set_temp }


    def outs_set_to_node_set(self, set_temp: Set[temp.Temp]) -> Set[graph.Node]:
        return { self.tnode(out) for out in set_temp }


    def temp_to_list(self, deffs: temp.TempList) -> List[graph.Node]:
        temp = deffs
        node_list = []
        while temp.head is not None:
            node_list.append(self.tnode(temp.head))
            temp = temp.tail

        return node_list

class Edge():

    edges_table = {}

    def __init__(self):
        super.__init__()
    
    def get_edge(self, origin_node: graph.Node, destiny_node: graph.Node) -> Edge:
        
        origin_table = Edge.edges_table.get(origin_node)
        destiny_table = Edge.edges_table.get(destiny_node)
        
        if (origin_table is None):
            origin_table = {}
            Edge.edges_table[origin_node] = origin_table

        if (destiny_table is None):
            destiny_table = {}
            Edge.edges_table[destiny_node] = destiny_table
        
        requested_edge: Edge  = origin_table.get(destiny_node)

        if(requested_edge is None):
            requested_edge = Edge()
            origin_table[destiny_node] = requested_edge
            destiny_table[origin_node] = requested_edge

        return requested_edge



class MoveList():

   def __init__(self, s: graph.Node, d: graph.Node, t: MoveList):
      self.src: graph.Node = s
      self.dst: graph.Node = d
      self.tail: MoveList = t