#include <cassert>

#include "bdd.h"

namespace bdd
{

void BDD::clear()
{
  if(node!=nullptr)
  {
    node->remove_reference();
    node=nullptr;
  }
}

void BDDnode::remove_reference()
{
  assert(reference_counter!=0);
  
  reference_counter--;

  if(reference_counter==0 && node_number>=2)
  {
    BDDManager::reverse_keyt reverse_key(var, low, high);
    mgr->reverse_map.erase(reverse_key);
    low.clear();
    high.clear();
  } 
}

BDD BDDManager::make_var(const std::string &label)
{
  var_table.push_back(var_table_entryt(label));
  true_bdd.node->var=var_table.size()+1;
  false_bdd.node->var=var_table.size()+1;
  return mk(var_table.size(), false_bdd, true_bdd);
}

bool equal_fkt(bool x, bool y)
{
  return x==y;
}

BDD BDD::operator ==(const BDD &other) const
{
  return apply(equal_fkt, *this, other);
}

bool xor_fkt(bool x, bool y)
{
  return x ^ y;
}

BDD BDD::operator ^(const BDD &other) const
{
  return apply(xor_fkt, *this, other);
}

BDD BDD::operator !() const
{
  return node->mgr->True() ^ *this;
}

bool and_fkt(bool x, bool y)
{
  return x && y;
}

BDD BDD::operator &(const BDD &other) const
{
  return apply(and_fkt, *this, other);
}

bool or_fkt(bool x, bool y)
{
  return x || y;
}

BDD BDD::operator |(const BDD &other) const
{
  return apply(or_fkt, *this, other);
}

BDDManager::BDDManager()
{
  // add true/false nodes
  append_node(0, 0, BDD(), BDD());
  false_bdd=BDD(&nodes.back());
  append_node(1, 1, BDD(), BDD());
  true_bdd=BDD(&nodes.back());
}

BDDManager::~BDDManager()
{
}

BDD BDDManager::mk(unsigned var, const BDD &low, const BDD &high)
{
  assert(var<=var_table.size());

  if(low.node_number()==high.node_number())
    return low;
  else
  {
    reverse_keyt reverse_key(var, low, high);
    reverse_mapt::const_iterator it=reverse_map.find(reverse_key);

    if(it!=reverse_map.end())
      return BDD(it->second);
    else
    {
      unsigned new_number=nodes.back().node_number+1;
      append_node(var, new_number, low, high);
      reverse_map[reverse_key]=&nodes.back();
      return BDD(&nodes.back());
    }
  }
}

bool operator < (const BDDManager::reverse_keyt &x,
                 const BDDManager::reverse_keyt &y)
{
  if(x.var<y.var) return true;
  if(x.var>y.var) return false;
  if(x.low<y.low) return true;
  if(x.low>y.low) return false;
  return x.high<y.high;
}

BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y)
{
  assert(x.node!=nullptr && y.node!=nullptr);
  assert(x.node->mgr==y.node->mgr);

  BDDManager *mgr=x.node->mgr;
  
  BDD u;

  if(x.is_constant() && y.is_constant())
    u=BDD(fkt(x.is_true(), y.is_true())?mgr->true_bdd:mgr->false_bdd);
  else if(x.var()==y.var())
    u=mgr->mk(x.var(),
              apply(fkt, x.low(), y.low()),
              apply(fkt, x.high(), y.high()));
  else if(x.var()<y.var())
    u=mgr->mk(x.var(),
              apply(fkt, x.low(), y),
              apply(fkt, x.high(), y));
  else /* x.var() > y.var() */
    u=mgr->mk(y.var(),
              apply(fkt, x, y.low()),
              apply(fkt, x, y.high()));
    
  return u;
}

}
