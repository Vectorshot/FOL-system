#include "head.h"

vector<string> str_split(const string& source, const string pattern) {
	regex re(pattern);
	return vector<string>(sregex_token_iterator(source.begin(), source.end(), re, -1), sregex_token_iterator());
}

class Predicate {
public:
	Predicate() = default;
	Predicate(string s) {//分割字符串
		if (s[0] == '~') {
            negation = true;
			s.erase(0, 1);
		}			
		vector<string> elements=str_split(s,"[,()\\s]+");
		name = elements[0];
		if (name[0] == '~')
			name.erase(0, 1);
		for (unsigned int i = 1; i < elements.size(); i++)
		{
			p_arguments.push_back(elements[i]);
			arguments_map[elements[i]].push_back(i - 1);
		}
	}
	string GetName() {
		return this->name;
	}
	bool IfNegated() {
		return this->negation;
	}
	vector<string> GetArguments() {
		return this->p_arguments;
	}
	string GetArgument(int i) {
		return this->p_arguments[i];
	}
	void SetName(string s) {
		this->name = s;
	}
	void SetNegation(bool a) {
		this->negation = a;
	}
	void InsertArgument(string s) {
		p_arguments.push_back(s);
	}
	void SetArgument(int i,string s) {
		this->p_arguments[i] = s;
	}
	int GetArguSize() {
		return p_arguments.size();
	}
	void Reverse() {
		if (this->negation)
			this->negation = false;
		else
		{
			this->negation = true;
		}
	}
	void ShowPredicate() {
		if (this->negation)
			cout << '~';
		cout << this->name << '(';
		for (int i = 0; i < p_arguments.size(); i++)
		{
			cout << p_arguments[i];
			if (i < p_arguments.size() - 1)
				cout << ',';
		}
		cout << ')';
	}
private:
	string name;
	bool negation = false;
	vector<string>p_arguments;
	unordered_map<string, vector<int>> arguments_map;
};

class Clause {
public:
	Clause() = default;
	Clause(string s) {
		bool flag = false;
		vector<string> elements = str_split(s, "[&=>\\s]+");
		if (s.find('=') != string::npos)
			flag = true;
		for (int i = 0; i < elements.size(); i++)
		{
			if (flag && (i < elements.size() - 1)) {
				if (elements[i][0] == '~')
					predicate_list.push_back(Predicate(elements[i].erase(0, 1)));
				else
				{
					predicate_list.push_back(Predicate('~' + elements[i]));
				}
			}				
			else
			{
				predicate_list.push_back(Predicate(elements[i]));
			}
		}
		for (int i = 0; i < predicate_list.size(); i++)
		{
			predicate_map[predicate_list[i].GetName()].push_back(i);
		}
	}
	void InsertPredicate(Predicate a) {
		predicate_list.push_back(a);
		predicate_map[a.GetName()].push_back(predicate_list.size()-1);
	}
	vector<Predicate> GetPredicates() {
		return this->predicate_list;
	}
	Predicate GetPredicate(int i) {
		return this->predicate_list[i];
	}
	int GetListSize() {
		return this->predicate_list.size();
	}
	vector<int> GetMapInfo(string a) {
		return this->predicate_map[a];
	}
	void IfUnsolved(bool a) {
		this->unsolvability = a;
	}
	bool ClauseCase() {
		return this->unsolvability;
	}
	void PredicateDelete(int i) {
		auto loc = predicate_list.begin() + i;
		this->predicate_list.erase(loc);
		this->predicate_map.clear();
	}
	void ClearList() {
		this->predicate_list.clear();
		this->predicate_map.clear();
	}

	void ResetMap() {
		for (int j = 0; j < predicate_list.size(); j++)
		{
			predicate_map[predicate_list[j].GetName()].push_back(j);
		}
	}
	void ShowClause() {
		for (int i = 0; i < predicate_list.size(); i++)
		{
			predicate_list[i].ShowPredicate();
			if (i < predicate_list.size() - 1)
				cout << '|';
		}
		cout << endl;
	}
private:
	vector<Predicate>predicate_list;
	unordered_map<string, vector<int>>predicate_map;
	bool unsolvability = false;//如果两个句子不能resolution，产生的predicate_list为空的clause的该变量为true
};

struct Substitution
{
	string var;//variable
	string val;//value
};

bool SinglePredicateResolution(Predicate a, Predicate b) {//两个predicate是否为Q(A)和~Q(A)形式
	if (a.GetArguSize()!=b.GetArguSize()||a.GetName()!=b.GetName()||a.IfNegated()==b.IfNegated())
	{
		return false;
	}
	else
	{
		for (int i = 0; i < a.GetArguSize(); i++)
		{
			if (a.GetArgument(i) != b.GetArgument(i))
				return false;
		}
	}
	return true;
}

bool IsPredicateSame(Predicate a, Predicate b) {//两个predicate是否相同
	if (a.GetArguSize() != b.GetArguSize() || a.GetName() != b.GetName() || a.IfNegated() != b.IfNegated())
	{
		return false;
	}
	else
	{
		for (int i = 0; i < a.GetArguSize(); i++)
		{
			if (a.GetArgument(i) != b.GetArgument(i))
				return false;
		}
	}
	return true;
}

bool IsAlwaysTrue(Clause a) {//永真式
	for (int i = 0; i < a.GetListSize(); i++)
	{
		Predicate temp_p(a.GetPredicate(i));
		vector<int> temp_map(a.GetMapInfo(temp_p.GetName()));
		if (temp_map.size() > 1) {
			for (int j = 0; j < temp_map.size(); j++)
			{
				if (SinglePredicateResolution(temp_p, a.GetPredicate(temp_map[j])))
					return true;
			}
		}
	}
	return false;
}

bool UnifyVar(string a, string b, unordered_map<string, string>& t);
bool SubUnify(string a, string b, unordered_map<string, string>& t) {
	if (a == b)
		return true;
	else if (a[0]>=97&&a[0]<=122)
	{
		return UnifyVar(a, b, t);
	}
	else if (b[0]>=97&&b[0]<=122)
	{
		return UnifyVar(b, a, t);
	}
	else
	{
		return false;
	}
}

bool UnifyVar(string a, string b, unordered_map<string, string>& t) {
	if (t[a].length()!=0) {
		return SubUnify(t[a], b, t);
	}
	else if (t[b].length()!= 0) {
		return SubUnify(a, t[b], t);
	}
	else
	{
		t[a] = b;
		return true;
	}
}
//两个predicate可以unify，返回的map不为空
//若返回map为空，有四种情况
//case1:a和b的argument数不同
//case2:a和b的negation相同(如P(x)和P(y),~Q(x)和~Q(y))
//case3:a和b无法unify(如P(A,B,x,y)和~P(x,y,B,A))
//case4:a和b正好可以互相resolution(如P(x,A)和~P(x,A))
unordered_map<string,string> Unify(Predicate a, Predicate b) {
	vector<string> varlist;
	unordered_map<string, string> submap;
	vector<string> argu_a(a.GetArguments());
	vector<string> argu_b(b.GetArguments());
	if (argu_a.size() != argu_b.size())
		return submap;
	if (a.IfNegated() == b.IfNegated())
		return submap;
	for (int i = 0; i < argu_a.size(); i++)
	{
		if(SubUnify(argu_a[i], argu_b[i], submap))
			continue;
		else
		{
			submap.clear();
			return submap;
		}
	}
	for (int i = 0; i < argu_a.size(); i++)
	{
		if (argu_a[i][0] >= 97 && argu_a[i][0] <= 122)
			varlist.push_back(argu_a[i]);
		if (argu_b[i][0] >= 97 && argu_b[i][0] <= 122)
			varlist.push_back(argu_b[i]);
	}
	for (int i = 0; i < varlist.size(); i++)
	{
		string temp = varlist[i];
		string temp1 = submap[varlist[i]];
		while (submap.count(temp))
		{
			if (submap[temp].length() != 0) {
				if (submap[temp][0] >= 65 && submap[temp][0] <= 90) {
					temp1 = submap[temp];
					break;
				}
				else
				{
					temp = submap[temp];
				}
			}
			else
			{
				break;
			}
		}
		submap[varlist[i]] = temp1;
	}
	return submap;
}

void RepeatedPredDelet(Clause& a) {
	if (a.GetListSize() < 2)
		return;
	vector<int> repeated;
	vector<Predicate> p_list;
	for (int i = 0; i < a.GetListSize()-1; i++)
	{
		for (int j = i+1; j < a.GetListSize(); j++)
		{
			if (IsPredicateSame(a.GetPredicate(i), a.GetPredicate(j))) {
				repeated.push_back(i);
			}
		}
	}
	for (int i = 0; i < a.GetListSize(); i++)
	{
		bool flag = true;
		for (int j = 0; j < repeated.size(); j++)
		{
			if (i == repeated[j]) {
				flag = false;
				break;
			}
		}
		if (flag)
		{
			p_list.push_back(a.GetPredicate(i));
		}
	}
	a.ClearList();
	for (int i = 0; i < p_list.size(); i++)
	{
		a.InsertPredicate(p_list[i]);
	}
}

Clause Unification(Clause a, Clause b) {//todo unify first,combine next
	Clause result;
	Clause new_a;
	Clause new_b;
	bool bloop = false;
	for (int i = 0; i < a.GetListSize(); i++)
	{
		vector<int> temp(b.GetMapInfo(a.GetPredicate(i).GetName()));//在clause b中找和a.GetPredicate(i)同名的predicate
		if (temp.size() == 0)
			continue;
		for (int j = 0; j < temp.size(); j++)
		{
			unordered_map<string, string> tempmap(Unify(a.GetPredicate(i),b.GetPredicate(temp[j])));
			//若tempmap为空并且两个predicate并非是正好可以互相resolution(如P(x,A)和~P(x,A))
			if (tempmap.size() == 0&&!SinglePredicateResolution(a.GetPredicate(i),b.GetPredicate(temp[j])))
				continue;
			else
			{
				int p1 = i;
				int p2 = temp[j];
				for (int k = 0; k < a.GetListSize(); k++)
				{
					Predicate temp(a.GetPredicate(k));
					for (int m = 0; m < temp.GetArguSize(); m++)
					{
						if (tempmap[temp.GetArgument(m)].length() != 0)
							temp.SetArgument(m, tempmap[temp.GetArgument(m)]);
					}
					new_a.InsertPredicate(temp);
				}
				for (int k = 0; k < b.GetListSize(); k++)
				{
					Predicate temp(b.GetPredicate(k));
					for (int m = 0; m < temp.GetArguSize(); m++)
					{
						if (tempmap[temp.GetArgument(m)].length() != 0)
							temp.SetArgument(m, tempmap[temp.GetArgument(m)]);
					}
					new_b.InsertPredicate(temp);
				}
				for (int i = 0; i < new_a.GetListSize(); i++)
				{
					if (!IsPredicateSame(new_a.GetPredicate(i), new_a.GetPredicate(p1)))
						result.InsertPredicate(new_a.GetPredicate(i));
				}
				for (int i = 0; i < new_b.GetListSize(); i++)
				{
					if (!IsPredicateSame(new_b.GetPredicate(i), new_b.GetPredicate(p2)))
						result.InsertPredicate(new_b.GetPredicate(i));
				}
				bloop = true;//用于跳出双层循环，也用于判断是不是两个clause可以resolution
				break;
			}
		}
		if (bloop)
		{
			break;
		}
	}
	if (bloop) {
		RepeatedPredDelet(result);
        return result;
	}		
	else
	{
		result.IfUnsolved(true);
		return result;
	}
}

bool IsSameClause(Clause a, Clause b);

bool IsSubset(Clause a, Clause b) {//判断a是否是b的子集
	unordered_map<int, int> match_map1;
	unordered_map<int, int> match_map2;
	if (a.GetListSize() >= b.GetListSize())
		return false;
	if (IsSameClause(a, b))//不加，自己消自己；加了，不能消除loop
		return false;//todo:在Resolution中消除重复的，只留下一个
	for (int i = 0; i < a.GetListSize(); i++)
	{
		for (int j = 0; j < b.GetListSize(); j++)
		{
			if (IsPredicateSame(a.GetPredicate(i), b.GetPredicate(j)) && match_map1[j] == 0) {
                match_map1[j] = i+1;
				match_map2[i] = j + 1;
			}				
		}	
	}
	for (int i = 0; i < a.GetListSize(); i++)
	{
		if (match_map2[i]==0)
		{
			return false;
		}
	}
	return true;
}

bool IsSameClause(Clause a, Clause b) {
	unordered_map<int, int> match_map1;
	unordered_map<int, int> match_map2;
	if (a.GetListSize() != b.GetListSize())
		return false;
	for (int i = 0; i < a.GetListSize(); i++)
	{
		for (int j = 0; j < b.GetListSize(); j++)
		{
			if (IsPredicateSame(a.GetPredicate(i), b.GetPredicate(j)) && match_map1[j] == 0) {
				match_map1[j] = i + 1;
				match_map2[i] = j + 1;
			}
		}
	}
	for (int i = 0; i < a.GetListSize(); i++)
	{
		if (match_map2[i] == 0)
		{
			return false;
		}
	}
	return true;
}

bool IsRepeatedInKB(Clause a,vector<Clause> kb) {
	for (int i = 0; i < kb.size(); i++)
	{
		if (IsSameClause(a, kb[i]))
			return true;
	}
	return false;
}

bool Resolution(Predicate a, vector<Clause> kb) {
	Clause query;
	a.Reverse();
	query.InsertPredicate(a);
	kb.push_back(query);
	queue<Clause> q_list;
	q_list.push(query);
	while (!q_list.empty())
	{
		vector<Clause> temp_q_list;
		while(!q_list.empty())
		{
			for (int j = 0; j < kb.size(); j++)
			{
				Clause temp(Unification(q_list.front(), kb[j]));
				//temp为两个clause进行resolution后产生的句子
				//如果两个clause产生的句子不包含predicate，有两种情况
				//case1:两个clause有contradiction
				//case2:两个clause无法进行resolution(没有可消的predicate)
				if (temp.GetListSize() == 0 && !temp.ClauseCase())
					return true;
				if (temp.GetListSize() != 0) {
					//永真式判断,重复判断
					if (IsAlwaysTrue(temp))
						continue;
					temp_q_list.push_back(temp);
				}
			}
			q_list.pop();
		}
		vector<Clause> temp_q_list_2;
		for (int i = 0; i < temp_q_list.size(); i++)
		{
			if ((!IsRepeatedInKB(temp_q_list[i], kb))&&(!IsRepeatedInKB(temp_q_list[i],temp_q_list_2)))//bug fix
				temp_q_list_2.push_back(temp_q_list[i]);
		}
		for (int i = 0; i < temp_q_list_2.size(); i++)
		{
			kb.push_back(temp_q_list_2[i]);
		}
		vector<Clause> kb_eliminate;
		vector<int> eliminate;
		for (int i = 0; i < kb.size(); i++)
		{
			for (int j = 0; j < kb.size(); j++)
			{
				if (IsSubset(kb[i],kb[j])&&i!=j)
				{
					kb_eliminate.push_back(kb[j]);
					eliminate.push_back(j);
				}
			}
		}
		vector<Clause> temp_kb;
		for (int i = 0; i < kb.size(); i++)
		{
			bool flag = false;
			for (int j = 0; j < eliminate.size(); j++)
			{
				if (i == eliminate[j]) {
					flag = true;
					break;
				}
			}
			if (!flag)
				temp_kb.push_back(kb[i]);
		}
		kb.clear();
		for (int i = 0; i < temp_kb.size(); i++)
		{
			kb.push_back(temp_kb[i]);
		}
		for (int i = 0; i < temp_q_list_2.size(); i++)
		{
			for (int j = 0; j < kb.size(); j++)
			{
				if (IsSameClause(temp_q_list_2[i], kb[j]))
					q_list.push(temp_q_list_2[i]);
			}
		}
	}
	return false;
}

int main()
{
	string line;
	ifstream infile("input.txt");
	int i = 0;
	int n = 0, k = 0;
	vector<Predicate> query;
	vector<Clause> knowledge_base;
	while (getline(infile,line))
	{
		if (i == 0)
			n = stoi(line);
		else if (n != 0 && i <= n)
			query.push_back(Predicate(line));
		else if (n!=0&&i==n+1)
		{
			k = stoi(line);
		}
		else if (k!=0&&i<=n+k+1)
		{
			knowledge_base.push_back(Clause(line));
		}
		i++;
	}
	ofstream savefile("output.txt");
	for (int i = 0; i < query.size(); i++)
	{
		if (Resolution(query[i], knowledge_base)) {
            savefile << "TRUE";
			//cout << "query " << i + 1 << endl;
		}			
		else
		{
			savefile << "FALSE";
			//cout << "query " << i + 1 << endl;
		}
		if (i < query.size() - 1)
			savefile << '\n';
	}
}
