import esprima
import escodegen
import random
import copy
import json
import os
import argparse

WRAPPER_TEMPLATE = """\
function __wrapper__(origFn, mutFn, origArgs, mutArgs) {
    const oVal = origFn(...origArgs);
    const mVal = mutFn(...mutArgs);
    console.assert(typeof oVal === typeof mVal, "Different") 
    return mVal;
}
"""

def js_to_ast(src):
    return esprima.parseScript(src, {
        'loc': True, 'range': True, 'comment': True, 'tokens': True
    }).toDict()

def ast_to_js(ast):
    return escodegen.generate(ast)

def collect_nodes(root):
    nodes, queue, seen = [], [(root, [])], set()
    while queue:
        node, path = queue.pop(0)
        if isinstance(node, dict):
            nid = id(node)
            if nid in seen: continue
            seen.add(nid)
            nodes.append((node, path))
            for k, v in node.items():
                if k in ('loc','range','tokens','comments'): continue
                if isinstance(v, (dict, list)):
                    queue.append((v, path + [k]))
        elif isinstance(node, list):
            for i, e in enumerate(node):
                if isinstance(e, (dict, list)):
                    queue.append((e, path + [i]))
    return nodes

def get_node(ast, path):
    n = ast
    for p in path:
        n = n[p]
    return n

def generate_variants_for_call(node):
    variants = []
    args = node.get('arguments') or []
    for idx in range(len(args)):
        s = ''.join(random.choices('abcdefghijklmnopqrstuvwxyz', k=random.randint(1,8)))
        variants.append((idx, {'type':'Literal','value':s,'raw':json.dumps(s)}))
        length = random.randint(1,5)
        elems = [{'type':'Literal','value':random.randint(0,9),'raw':str(random.randint(0,9))} for _ in range(length)]
        variants.append((idx, {'type':'ArrayExpression','elements':elems}))
        props = []
        for _ in range(random.randint(1,3)):
            key = ''.join(random.choices('xyzuvw', k=3))
            props.append({
                'type':'Property',
                'key':{'type':'Identifier','name':key},
                'value':random.choice(elems),
                'kind':'init','method':False,'shorthand':False,'computed':False
            })
        variants.append((idx, {'type':'ObjectExpression','properties':props}))
        variants.append((idx, {
            'type':'FunctionExpression','id':None,'params':[],
            'body':{'type':'BlockStatement','body':[]},
            'generator':False,'expression':False,'async':False
        }))
    return variants

def mutate_binop(info):
    n=info['node']
    if n.get('type')=='BinaryExpression':
        m={'+':'-','-':'+','*':'/','/':'*','>':'<=','<':'>=','>=':'<','<=':'>','==':'!=','!=':'==','===':'!==','!==':'===','|':'&','&':'|','^':'&','<<':'>>','>>':'<<'}
        op=n['operator']
        if op in m:
            n['operator']=m[op]; return True
    return False

def mutate_boolean(info):
    n=info['node']
    if n.get('type')=='Literal' and isinstance(n.get('value'),bool):
        n['value']=not n['value']; n['raw']=str(n['value']).lower(); return True
    return False

def mutate_number(info):
    n=info['node']
    if n.get('type')=='Literal' and isinstance(n.get('value'),(int,float)):
        v=n['value']
        if v in (0,1):
            n['value'],n['raw']=(1,'1') if v==0 else (0,'0'); return True
        if random.random()<0.5:
            nv=round(v*0.5) or 1
            n['value'],n['raw']=nv,str(nv); return True
        n.clear()
        n.update({'type':'UnaryExpression','operator':'-','prefix':True,'argument':{'type':'Literal','value':v,'raw':str(v)}})
        return True
    return False

def mutate_logicop(info):
    n=info['node']
    if n.get('type')=='LogicalExpression':
        m={'&&':'||','||':'&&'}
        op=n['operator']
        if op in m:
            n['operator']=m[op]; return True
    return False

def mutate_update(info):
    n=info['node']
    if n.get('type')=='UpdateExpression':
        m={'++':'--','--':'++'}
        op=n['operator']
        if op in m:
            n['operator']=m[op]; return True
    return False

def mutate_negation(info):
    n=info['node']
    if n.get('type')=='IfStatement':
        t=n['test']
        if t.get('type')=='UnaryExpression' and t.get('operator')=='!':
            n['test']=copy.deepcopy(t['argument'])
        else:
            n['test']={'type':'UnaryExpression','operator':'!','prefix':True,'argument':copy.deepcopy(t)}
        return True
    return False

def mutate_remove_else(info):
    n=info['node']
    if n.get('type')=='IfStatement' and n.get('alternate') is not None:
        n['alternate']=None; return True
    return False

def mutate_return(info):
    n=info['node']
    if n.get('type')=='ReturnStatement':
        c=random.choice(['null','undefined'])
        if c=='null':
            n['argument']={'type':'Literal','value':None,'raw':'null'}
        else:
            n['argument']={'type':'Identifier','name':'undefined'}
        return True
    return False

def mutate_assign(info):
    n=info['node']
    if n.get('type')=='AssignmentExpression':
        ops=['=','+=','-=','*=','/=']
        ch=[o for o in ops if o!=n['operator']]
        if ch:
            n['operator']=random.choice(ch); return True
    return False

def mutate_call_swap(info):
    n=info['node']
    if n.get('type')=='CallExpression':
        a=n.get('arguments') or []
        if len(a)>=2:
            i,j=random.sample(range(len(a)),2)
            a[i],a[j]=a[j],a[i]; return True
    return False

MUTATORS=[mutate_binop,mutate_boolean,mutate_number,mutate_logicop,
          mutate_update,mutate_negation,mutate_remove_else,
          mutate_return,mutate_assign,mutate_call_swap]

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('-s','--source',required=True)
    p.add_argument('-o','--outdir',required=True)
    args=p.parse_args()
    os.makedirs(args.outdir,exist_ok=True)

    for fn in os.listdir(args.source):
        if not fn.endswith('.js'): continue
        code=open(os.path.join(args.source,fn),encoding='utf8').read()
        ast0=js_to_ast(code)

        call_args_map={}
        for node,path in collect_nodes(ast0):
            if node.get('type')=='CallExpression' and node.get('callee',{}).get('type')=='Identifier' and node['callee']['name']!='__wrapper__':
                rng=tuple(node.get('range',[]))
                call_args_map[rng]=copy.deepcopy(node.get('arguments') or [])

        originals=[s for s in ast0['body'] if s.get('type')=='FunctionDeclaration' and s.get('id')]
        ast0['body']=[s for s in ast0['body'] if not(s.get('type')=='FunctionDeclaration' and s.get('id'))]

        for orig in originals:
            nm=orig['id']['name']
            cpy=copy.deepcopy(orig)
            cpy['id']['name']='mutated_'+nm
            ast0['body'].insert(0,cpy)

        mutants=[]
        for node,path in collect_nodes(ast0):
            if node.get('type')=='CallExpression':
                for idx,var in generate_variants_for_call(node):
                    c=copy.deepcopy(ast0)
                    get_node(c,path)['arguments'][idx]=var
                    mutants.append(c)
            for m in MUTATORS:
                c=copy.deepcopy(ast0)
                tgt=get_node(c,path)
                before=json.dumps(tgt,sort_keys=True)
                if m({'node':tgt}):
                    after=json.dumps(tgt,sort_keys=True)
                    if before!=after:
                        mutants.append(c)

        base=os.path.splitext(fn)[0]
        for i,m_ast in enumerate(mutants,1):
            m_ast['body']=[copy.deepcopy(o) for o in originals]+m_ast['body']
            for node,_ in collect_nodes(m_ast):
                if not isinstance(node, dict): continue
                if node.get('type')!='CallExpression': continue
                cal=node.get('callee',{}) or {}
                if cal.get('type')!='Identifier': continue
                name=cal['name']
                if any(o['id']['name']==name for o in originals):
                    rng=tuple(node.get('range',[]))
                    orig_args = call_args_map.get(rng, copy.deepcopy(node.get('arguments') or []))
                    mut_args  = copy.deepcopy(node.get('arguments') or [])
                    node.clear()
                    node.update({
                        'type':'CallExpression',
                        'callee':{'type':'Identifier','name':'__wrapper__'},
                        'arguments':[
                            {'type':'Identifier','name':name},
                            {'type':'Identifier','name':'mutated_'+name},
                            {'type':'ArrayExpression','elements':orig_args},
                            {'type':'ArrayExpression','elements':mut_args}
                        ]
                    })
            out_js=WRAPPER_TEMPLATE+"\n"+ast_to_js(m_ast)
            out_name=f"{base}_mutant_{i}.js"
            with open(os.path.join(args.outdir,out_name),'w',encoding='utf8') as f:
                f.write(out_js)
    print("finish")

