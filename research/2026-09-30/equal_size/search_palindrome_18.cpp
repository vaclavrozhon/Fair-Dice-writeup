#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
using V=array<int,24>;
int main(){
 vector<string> pats={""};
 for(int k=1;k<=4;k++){
  string p="0123";
  do {string s=p.substr(0,k); if(find(pats.begin(),pats.end(),s)==pats.end())pats.push_back(s);}while(next_permutation(p.begin(),p.end()));
 }
 array<vector<pair<int,int>>,4> updates;
 for(int j=1;j<(int)pats.size();j++){
  string s=pats[j], pre=s.substr(0,s.size()-1);
  int i=find(pats.begin(),pats.end(),pre)-pats.begin();
  updates[s.back()-'0'].push_back({j,i});
 }
 auto counts=[&](const string&w){
  array<int,65> d{};d[0]=1;
  for(char x:w)for(auto [j,i]:updates[x-'0'])d[j]+=d[i];
  return d;
 };
 vector<string> blocks;string p="0123";
 do{string q=p;reverse(q.begin(),q.end());blocks.push_back(p+q);}while(next_permutation(p.begin(),p.end()));
 map<V,string> catalog;
 int fair3=0;
 for(auto&a:blocks)for(auto&b:blocks)for(auto&c:blocks){
  string w=a+b+c;auto d=counts(w);bool fair=true;
  for(int j=0;j<65;j++)if(pats[j].size()==3&&d[j]!=36){fair=false;break;}
  if(!fair)continue;
  fair3++;V v;int q=0;
  for(int j=0;j<65;j++)if(pats[j].size()==4)v[q++]=d[j]-54;
  catalog.emplace(v,w);
 }
 cout<<"{\"three_fair_blocks\":"<<fair3<<",\"distinct_defects\":"<<catalog.size()<<"}"<<endl;
 for(const auto&[a,wa]:catalog)for(const auto&[b,wb]:catalog){
  V c;for(int i=0;i<24;i++)c[i]=-a[i]-b[i];
  auto it=catalog.find(c);if(it==catalog.end())continue;
  string w=wa+wb+it->second;auto d=counts(w);bool ok=true;
  for(int j=0;j<65;j++)if(pats[j].size()==4&&d[j]!=4374)ok=false;
  cout<<"{\"word\":\""<<w<<"\",\"full_order_check\":"<<(ok?"true":"false")<<"}"<<endl;
  return ok?0:2;
 }
 cout<<"{\"three_block_sum_zero\":false}"<<endl;
}
