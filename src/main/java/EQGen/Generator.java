/**
 * MIT License

Copyright (c) 2019 Mehmet Aziz Yirik

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
 */


package EQGen;

import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.text.DecimalFormat;

import org.apache.commons.cli.*;
import org.openscience.cdk.exception.CDKException;
import org.openscience.cdk.graph.ConnectivityChecker;
import org.openscience.cdk.graph.GraphUtil;
import org.openscience.cdk.graph.invariant.Canon;
import org.openscience.cdk.group.AtomContainerDiscretePartitionRefiner;
import org.openscience.cdk.group.Partition;
import org.openscience.cdk.group.PartitionRefinement;
import org.openscience.cdk.group.Permutation;
import org.openscience.cdk.group.PermutationGroup;
import org.openscience.cdk.inchi.InChIGeneratorFactory;
import org.openscience.cdk.interfaces.IAtom;
import org.openscience.cdk.interfaces.IAtomContainer;
import org.openscience.cdk.interfaces.IBond;
import org.openscience.cdk.interfaces.IBond.Order;
import org.openscience.cdk.io.SDFWriter;
import org.openscience.cdk.io.iterator.IteratingSDFReader;
import org.openscience.cdk.silent.Atom;
import org.openscience.cdk.depict.DepictionGenerator;
import org.openscience.cdk.silent.SilentChemObjectBuilder;
import org.openscience.cdk.tools.SaturationChecker;
import org.openscience.cdk.tools.manipulator.BondManipulator;

import com.google.common.collect.ListMultimap;
import com.google.common.collect.MultimapBuilder;


public class Generator {
	public static Set<String> inchiCheck = new HashSet<String>();
	public static Set<String> classInchiCheck= new HashSet<String>();
	public static Set<String> atomSatInchiCheck= new HashSet<String>();
	public static Set<String> atomsat = new HashSet<String>();
	public static SaturationChecker saturation;
	public static ConnectivityChecker conCheck;
	public static ArrayList<Integer> hydrogens= new ArrayList<Integer>();
	public static boolean verbose = false;
	static String fragments = null;
	static String filedir = null;
	static String molinfo= null;
	public static Map<String, Integer> valences; 
	static {
		//The atom valences from CDK.
		valences = new HashMap<String, Integer>();
			
		valences.put("C", 4);
		valences.put("N", 5);
		valences.put("O", 2);
		valences.put("S", 6);
		valences.put("P", 5);
		valences.put("F", 1);
		valences.put("I", 1);
		valences.put("Cl", 1);
		valences.put("Br", 1);
		valences.put("H", 1);
	}
	
	/**
	 * Comparators.
	 */
	
	public static final Comparator<String> ASC_ORDERS = new Comparator<String>() {
	    public int compare(String e1, String e2) { 
	        return -e2.compareTo(e1);
	    }
	};
	
	public static final Comparator<Integer> ASC_ORDERI = new Comparator<Integer>() {
	    public int compare(Integer e1, Integer e2) { 
	        return -e2.compareTo(e1);
	    }
	};
	
	/**
	 * General Functions
	 */
	
	/**
	 * Checks an int array is in the list or not.
	 * @param list ArrayList of int arrays
	 * @param arr int array
	 * @return boolean true if the array is in the list
	 */
	
	public static boolean inTheList(ArrayList<int[]> list, int[] arr) {
		boolean check= false;
		for(int i=0;i<list.size();i++) {
			if(Arrays.equals(list.get(i), arr)) {
				check=true;
				break;
			}
		}
		return check;
	}
	
	/**
	 * Sum all array entries.
	 * @param array int array
	 * @return
	 */
	
	public static int sum(int[] array) {
		int sum=0;
		for(int i=0;i<array.length;i++) {
			sum=sum+array[i];
		}
		return sum;
	}
	
	/**
	 * Sum array entries until the given index
	 * @param array int array
	 * @return
	 */
	
	public static int sum(int[] array, int index) {
		int sum=0;
		for(int i=0;i<=index;i++) {
			sum=sum+array[i];
		}
		return sum;
	}
	/**
	 * Checks whether the list is in the list of the lists or not.
	 * @param list List of ArrayList<Integer>
	 * @param arr list of integers
	 * @return true if the list is in the list of lists.
	 */
	
	public static boolean inTheList(HashSet<ArrayList<Integer>> list, ArrayList<Integer> arr) {
		 boolean check= false;
		 for(ArrayList<Integer> l:list) {
			 if(l.equals(arr)) {
				 check=true;
				 break;
			 }
		 }
		 return check;
	 }
	
	/**
	 * Removing an index from a list, then updating it.
	 * @param list integer list
	 * @param index index to remove.
	 * @return List<Integer> new integer list
	 */
	
	public static List<Integer> updateList(List<Integer> list, int index){
		List<Integer> listNew= new ArrayList<Integer>();
		for(Integer j:list) {
			listNew.add(j);
		}
		listNew.remove((Integer)index);
		return listNew;
	}
	
	/**
	 * To check in a list of integers, what the open sites in a given molecule.
	 * @param mol
	 * @param list
	 * @return
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<Integer> openSites(IAtomContainer mol, List<Integer> list) throws CloneNotSupportedException, CDKException, IOException{
		for(Integer i: list) {
			if(!saturationChecker(mol,i)) {
				List<Integer> newList= updateList(list,i);
				list=newList;
			}
		}
		return list;
	}
	
	/**
	 * Molecule Depiction
	 * @param mol atom container
	 * @param path directory path for png file.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static void depict(IAtomContainer mol, String path) throws CloneNotSupportedException, CDKException, IOException{
		DepictionGenerator depict = new DepictionGenerator();
		depict.withCarbonSymbols().withSize(1000, 1000).withZoom(4).depict(mol).writeTo(path);
	}
	
	/**
	 * *******************************************************************************
	 */
	
	/**
	 * Permutation Group Functions - Fundamental Lemma of Orbits
	 * More details: Mathematical Chemistry and Cheminformatics book.
	 */
	
	/**
	  * Generating list of unique orbits for the list of truncated tabloids
	  * and the acting group.The method is given in MOLGEN Book Page 80. 
	  * The method is explained also with an example (Example 3.31) Page 167.
	  * 
	  * 
	  * @param truncated truncated tabloids for the acting group
	  * @param group a permutation group 
	  * @return list of unique orbits
	  */
	 
	 public static Set<Set<ArrayList<Integer>>> fundamentalLemma(PermutationGroup group, PermutationGroup group2, int trun, ArrayList<Permutation> group3) {
		 Set<Set<ArrayList<Integer>>> orbits= new HashSet<Set<ArrayList<Integer>>>(); 
		 List<int[]> list= new ArrayList<int[]>();
		 int[] array= new int[0];
		 List<int[]> truncated= truncatedTabloidsInitial(trun,array,list);
		 for(int j=0;j<truncated.size();j++) {
			Set<ArrayList<Integer>> orbit= new HashSet<ArrayList<Integer>>();
		    for(Permutation perm: group3) {
		    	ArrayList<Integer> l= new ArrayList<Integer>();
		    	for(int k=0;k<truncated.get(j).length;k++) {
		    		l.add(perm.get(truncated.get(j)[k]));
		    	}
		    	l.sort(ASC_ORDERI);
		    	orbit.add(l);
		    }
		    orbits.add(orbit);
		  }
		 
		 return orbits;
	 }
	  
	 /**
	  * Generating a group from a list permutations
	  * @param perm a list of permutations	
	  * @return permutation group generated by a list of permutations
	  */
			
	public static PermutationGroup generateGroup(ArrayList<Permutation> list) {
		List<Permutation> generators = new ArrayList<Permutation>();
		generators.addAll(list);
		return new PermutationGroup(8, generators); // TODO: Size should be automatically given not manual
	}
	
	public static int[] addElement(int[] a, int e) {
		a  = Arrays.copyOf(a, a.length + 1);
	    a[a.length - 1] = e;
	    return a;
	}
	 
	 /**
	  * Truncated tabs are described in Mathematical Chemistry and Cheminformatics book. (Chapter 3)
	  * @param number
	  * @param array
	  * @param list
	  * @return list of int arrays, tabs.
	  */
	 
	 public static List<int[]> truncatedTabloidsInitial(int number, int[] array, List<int[]> list) {
		int size= array.length;
		if(size==number) {
			list.add(array);
		}else {
			if(size==0) {
				for(int i=0; i<=number;i++) {
					truncatedTabloidsInitial(number,addElement(array,i),list);
				}
			}else {
				for(int i=array[size-1]+1; i<=number+size;i++) {
					truncatedTabloidsInitial(number,addElement(array,i),list);
				}
			}
		}
		return list;
	 }
	 
	 public static List<int[]> truncatedTabloids(int number, int[] array, List<int[]> list, List<Integer> entries) {
		 int size= array.length;
		 if(size==number) {
			 list.add(array);
		 }else {
			for(Integer i:entries) {
				entries=updateList(entries,i);
				truncatedTabloids(number,addElement(array,i),list,entries);
			}
		 }
		 return list;
	 }
	 
	 
	 public static List<Integer> inputList(int[] array, int number){
		 List<Integer> intList= new ArrayList<Integer>();
		 for(int i=1;i<=number;i++) {
			 if(!entryCheck(array,i)) {
				 intList.add(i);
			 }
		 }
		 return intList;
	 }
	 
	 public static boolean entryCheck(int[] array, int entry) {
		 boolean check=false;
		 for(int i=0;i<array.length;i++) {
			 if(array[i]==entry) {
				 check=true;
				 break;
			 }
		 }
		 return check;
	 }
	 
	 /**
	  * For the atoms with valence 1, To count occurences of atom types in an atom container.
	  * @param mol atom container
	  * @return HashMap of atom occurunces.
	  */
	 
	 public static HashMap<String,Integer> atomsWithValence1(IAtomContainer mol){
		 HashMap<String, Integer> atomCounts = new HashMap<String, Integer>(); 
		 for(IAtom atom: mol.atoms()) {
			 String symbol = atom.getSymbol();
			 if(valences.get(symbol)==1) {
				 if(atomCounts.containsKey(symbol)) {
					 atomCounts.put(symbol, atomCounts.get(symbol)+1);
				 }else {
					 atomCounts.put(symbol, 1);
				 }
			 }
		 }
		 return atomCounts; 
	 }
	 
	 /**
	  * To sort a Hashmap based on the entries. 
	  * @param atomCounts HashMap<String,Integer>
	  * @return HashMap<String, Integer>
	  */
	 
	 public static HashMap<String, Integer> sortByValue(HashMap<String, Integer> atomCounts) { 
	     List<Map.Entry<String, Integer> > map2list = new LinkedList<Map.Entry<String, Integer>>(atomCounts.entrySet()); 
	     Collections.sort(map2list, new Comparator<Map.Entry<String, Integer> >() { 
	    	 public int compare(Map.Entry<String, Integer> o1, Map.Entry<String, Integer> o2){ 
	    		 return (o1.getValue()).compareTo(o2.getValue()); 
	         } 
	     }); 
	          
	     HashMap<String, Integer> newMap = new LinkedHashMap<String, Integer>(); 
	     for (Map.Entry<String, Integer> entry : map2list) { 
	    	 newMap.put(entry.getKey(), entry.getValue()); 
	     } 
	     return newMap; 
	 } 
	 
	 public static List<int[]> truncatedTabloids(int[] entries){
		 List<int[]> tabloids= new ArrayList<int[]>();
		 for(int i=0;i<entries.length-1;i++) {
			 if(i==0) {
				 int[] array= new int[0];
				 tabloids = truncatedTabloidsInitial(entries[0],array,tabloids);
			 }else {
				 tabloids = truncatedTabloids(tabloids,sum(entries,i),sum(entries)); 
			 }
		 }
		 return tabloids;
	 }
	 
	public static List<int[]> truncatedTabloids(List<int[]> tabloids,int number, int total){
		List<int[]> tabloids2= new ArrayList<int[]>();
		for(int[] tab: tabloids) {
			truncatedTabloids(number,tab,tabloids2,inputList(tab,total));
		}
		return tabloids2;
	}
	 
	/**
	 * New equivalence classes method based on molecule automorphism group 
	 */
	
	public static PermutationGroup getAutomorphismGroup(IAtomContainer ac) {
		AtomContainerDiscretePartitionRefiner refiner = PartitionRefinement.forAtoms().create();
		return refiner.getAutomorphismGroup(ac);
	}
	
	public static Partition getAutomorphismPartition(IAtomContainer molecule) {
		AtomContainerDiscretePartitionRefiner refiner = PartitionRefinement.forAtoms().create();
		return refiner.getAutomorphismPartition(molecule);
	}
	
	/**
	 * Get the orbits, the equivalence classes of the atoms. 
	 */
	
	public static Set<Set<Integer>> getOrbits(IAtomContainer ac, ArrayList<Integer> heteroIndices){
		PermutationGroup group=getAutomorphismGroup(ac);
		Set<Set<Integer>> orbits= new HashSet<Set<Integer>>();
		for(Integer i: heteroIndices) {
			orbits.add(getOrbit(group,i));
		}
		return orbits;
	}
	
	public static Set<Integer> getOrbit(PermutationGroup group, Integer i){
		Set<Integer> orbit = new HashSet<Integer>();
		for(Permutation perm: group.all()) {
			int n= perm.get(i);
			if(!orbit.contains(n)) {
				orbit.add(n);
			}
		}
		return orbit;
	}
	
	/**
	 * *******************************************************************************
	 */
	
	/**
	 * Atom container functions
	 */
	
	/**
	 * Building an atom container from a string of atom-implicit hydrogen information.
	 * If provided, fragments are also added.
	 * @param mol molecular information
	 * @return atom container new atom container
	 * @throws IOException
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 */
	
	public static IAtomContainer build(String mol) throws IOException, CloneNotSupportedException, CDKException {
		IAtomContainer atomcontainer = new org.openscience.cdk.silent.AtomContainer();
		List<String> symbols = new ArrayList<String>();
	    List<Integer> hydrogens = new ArrayList<Integer>();
	    String[] atoms = mol.split("(?=[A-Z])");
	    for (String atom : atoms) {
	    	String[] info = atom.split("(?=[0-9])", 2);   
	        symbols.add(info[0]);
	        hydrogens.add(info.length > 1 ? Integer.parseInt(info[1]):0);
	    }
	    for(int i=0;i<symbols.size();i++) {
	        atomcontainer.addAtom(new Atom(symbols.get(i)));
	        atomcontainer.getAtom(i).setImplicitHydrogenCount(hydrogens.get(i));
	    }
	    //setFlagID(atomcontainer);
	    //addFragments(atomcontainer,fragments);
	    return atomcontainer;
	}
	
	/**
	 * In an atomcontainer counting hydrogens.
	 * @param ac IAtomContainer
	 * @param index atom index
	 * @return
	 */
	
	public static int countHydrogen(IAtomContainer ac, int index) {
		int count=0;
		List<IAtom> list=ac.getConnectedAtomsList(ac.getAtom(index));
		for(IAtom atom: list) {
			if(atom.getSymbol().equals("H")) {
				count++;
			}
		}
		return count;
	}
	
	/**
	 * Setting flag for each atom in the atomcontainer for fragment construction. 
	 * @param ac atom container
	 */
	
	public static void setFlag(IAtomContainer ac) {
		for(IAtom atom: ac.atoms()) {
			atom.setFlag(1, false);
		}
	}
	
	/**
	 * Setting flag IDs for each atom in the atomcontainer for fragment construction. 
	 * @param ac atom container
	 */
	
	public static void setFlagID(IAtomContainer ac){
		for(int i=0;i<ac.getAtomCount();i++) {
			IAtom atom= ac.getAtom(i);
			atom.setFlag(1, false);
			atom.setID("no:"+i);
		}
	}
	
	/**
	 * Getting equal atoms in atom container and a fragment.
	 * @param acon atom container
	 * @param fragment fragment
	 * @return int array with the indices of the equal atoms.
	 */
	
	public static int[] getEqualAtoms(IAtomContainer acon, IAtomContainer fragment) {
		int[] equal= new int[fragment.getAtomCount()];
		for(IAtom fAtom : fragment.atoms()){
			for(IAtom atom : acon.atoms()){
				if(fAtom.getSymbol().equals(atom.getSymbol())&& fAtom.getImplicitHydrogenCount()==atom.getImplicitHydrogenCount() && (!fAtom.getFlag(1))&&(!atom.getFlag(1))){
					fAtom.setID(atom.getID());
					equal[fragment.indexOf(fAtom)]=acon.indexOf(atom);
					fAtom.setFlag(1, true);
					atom.setFlag(1, true);
					break;
				}
			}
		}
		return equal;
	}
	
	/**
	 * Adding fragments of the molecule.
	 * @param acontainer atom container
	 * @param fpath directory path for fragments file.
	 * @throws IOException
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 */
	
	public static void addFragments(IAtomContainer acontainer, String fragmentsPath) throws IOException, CloneNotSupportedException, CDKException{
		IteratingSDFReader fragments = new IteratingSDFReader(new FileReader(fragmentsPath),SilentChemObjectBuilder.getInstance());
		while (fragments.hasNext()) {
			IAtomContainer fragment=fragments.next();
			setFlag(acontainer);
			List<IAtom> done= new ArrayList<IAtom>();
			int[] equals= getEqualAtoms(acontainer,fragment);
			for(int i=0;i<equals.length;i++) {
				List<IAtom> neighbors = fragment.getConnectedAtomsList(fragment.getAtom(i));
				for(IAtom neig: neighbors){
					if(!done.contains(neig)){
						for(int j=0;j<acontainer.getAtomCount();j++){
							if(neig.getID().equals(acontainer.getAtom(j).getID())){
								done.add(fragment.getAtom(i));
								acontainer.addBond(equals[i], j,fragment.getBond(fragment.getAtom(i), neig).getOrder());
							}
						}
					}
				}
				
			}
		}
		fragments.close();
	}
	
	/**
	 * Calculating the total number of bonds connecting to the atom.
	 * @param mol atom container
	 * @param i atom index
	 * @return int summation of all bond orders for the atom.
	 */
	
	public static int getTotalBondOrder(IAtomContainer mol, int i){
		int count=0;
		for(IBond bond: mol.getConnectedBondsList(mol.getAtom(i))){
			count=count+bond.getOrder().numeric();
		}
		return count;
	}
	
	/**
	 * The equivalent classes of molecules are ordered and enumerated in ascending order 
	 * based on their open values and implicit hydrogens; as described in the paper. 
	 * @param acontainer atom container
	 * @return ListMultiMap map of atom equivalence classes
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static ListMultimap<String,Integer> equivalenceClass(IAtomContainer molecule) throws CloneNotSupportedException, CDKException, IOException {
		ListMultimap<String,Integer> equivalenceClasses = MultimapBuilder.treeKeys(ASC_ORDERS).arrayListValues().build();
		long[] symmetryClasses=canonSymmetry(molecule);
		for(int index=0; index<molecule.getAtomCount();index++){
			if(saturationChecker(molecule, index)==true){	
				String label = molecule.getAtom(index).getSymbol()+openSiteCounter(molecule, index)+Long.valueOf(symmetryClasses[index]).intValue();
				equivalenceClasses.put(label, index); //The open sites and the symmetry values are used for labelling.
			}
		}		
		return equivalenceClasses;
	}
	
	/**
	 * Number of neighbors an atom has in a atomcontainer
	 * @param molecule IAtomContainer
	 * @param atom 
	 * @return
	 */
	
	public static int neighbors(IAtomContainer molecule, IAtom atom) {
		return molecule.getConnectedAtomsList(atom).size();
	}
	
	/**
	 * Generating symmetry classes of atoms with Canon class.
	 * @param ac atom container
	 * @return long[] list of atom equivalence classes
	 */
	
	public static long[] canonSymmetry(IAtomContainer ac) {
		 int[][] g = GraphUtil.toAdjList(ac);
		 return Canon.symmetry(ac, g);
	}
	
	/**
	 * InChI Generator from CDK.
	 * @param molecule IAtomContainer
	 * @return
	 * @throws CDKException
	 */
	
	public static String inchiGeneration(IAtomContainer molecule) throws CDKException {
		String inchi = InChIGeneratorFactory.getInstance().getInChIGenerator(molecule).getInchi();	
		return inchi;
	}
	
	/**
	 * Count open sites of an atom in a molecule.
	 * @param mol atom container
	 * @param i atom index
	 * @return int number of open sites
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static int openSiteCounter(IAtomContainer mol, int i)throws CloneNotSupportedException, CDKException, IOException{
		int open=0;
		if(mol.getAtom(i).getImplicitHydrogenCount()==null) {
			open += valences.get(mol.getAtom(i).getSymbol()).intValue()- orderSum(mol,i);
		}else {
			open += valences.get(mol.getAtom(i).getSymbol()).intValue()- orderSum(mol,i) - mol.getAtom(i).getImplicitHydrogenCount(); 
		}
		//int open = valences.get(mol.getAtom(i).getSymbol()).intValue() - orderSum(mol,i) - ; 
		return open;
	}
	
	/**
	 * Sum all connected bond orders for an atom.
	 * @param mol atom container 
	 * @param i an atom index
	 * @return int sumation of bond orders.
	 */
	
	public static int orderSum(IAtomContainer mol, int i){
		int count=0;
		for(IBond bond: mol.getConnectedBondsList(mol.getAtom(i))){
			count=count+bond.getOrder().numeric();
		}
		return count;
	}
	
	/**
	 * Saturation Checkers.
	 */
	
	/**
	 * Saturation checker for a atomcontainer
	 * @param mol
	 * @return
	 * @throws CDKException
	 */
	
	public static boolean saturation(IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		return saturation.allSaturated(mol);
	}
	
	/**
	 * In the atom container, checking an atom is saturated or not.
	 * @param mol atom container
	 * @param i atom index
	 * @return boolean true if atom is saturated.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static boolean saturationChecker(IAtomContainer mol, int i) throws CloneNotSupportedException, CDKException, IOException{
		if(mol.getAtom(i).getImplicitHydrogenCount()==null) {
			if ((getTotalBondOrder(mol,i))>= (int)valences.get(mol.getAtom(i).getSymbol())){ 
				return false;
			}else{
				return true;
			}
		}else {
			if ((mol.getAtom(i).getImplicitHydrogenCount()+getTotalBondOrder(mol,i))>= (int)valences.get(mol.getAtom(i).getSymbol())){ 
				return false;
			}else{
				return true;
			}
		}
	}
	
	/**
	 * Checking saturation of a list of atoms in a molecule.
	 * @param list list of atoms
	 * @param mol atom container
	 * @return boolean true if all atoms are saturated.
	 * @throws CDKException
	 */
	
	public static boolean allSaturated(List<IAtom> list, IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		boolean check=true;
		for(IAtom atom:list) {
			if(!saturation.isSaturated(atom, mol)) {
				check=false;
				break;
			}
		}
		return check;
	}
	
	
	/**
	 * Checks whether the atom container has any saturated substructures.
	 * @param mol atom container
	 * @return boolean true if there is a saturated substructure.
	 * @throws CDKException
	 */
	
	public static boolean subSaturation(IAtomContainer mol) throws CDKException {
		saturation= new SaturationChecker();
		boolean check=false;
		if(!saturation.isSaturated(mol)) {
			for(IAtom atom:mol.atoms()) {
				List<IAtom> atoms= new ArrayList<IAtom>();
				atoms.add(atom);
				check=subSaturation(mol,atom,atoms);
				if(check) {
					break;
				}
			}
		}
		return check;
	}
	
	/**
	 * Sub function for subSaturation function.Checking whether the neighbors of the atom are
	 * saturated or not.
	 * @param mol atom container
	 * @param atom atom 
	 * @param atoms list of atoms
	 * @return boolean true if there is a saturated substructure for the list of atoms.
	 * @throws CDKException
	 */
	
	public static boolean subSaturation(IAtomContainer mol, IAtom atom, List<IAtom> atoms) throws CDKException {
		boolean check=true;
		saturation= new SaturationChecker();
		if(saturation.isSaturated(mol)) {
			check=true;
		}else {
			if(saturation.isSaturated(atom, mol)) {
				List<IAtom> nei= mol.getConnectedAtomsList(atom);
				nei.removeAll(atoms);
				if(allSaturated(nei,mol)) {
					for(IAtom atom2:nei) {
						atoms.add(atom2);
						subSaturation(mol,atom2,atoms);
					}
				}else {
					check=false;
				}
			}
			else {
				check=false;
			}
		}
		return check;
	}
	
	/**
	 * To check connectivity of a saturated molecule before writing it to the output file.
	 * @param mol IAtomContainer 
	 * @return
	 */
	
	public static boolean connectivityCheck(IAtomContainer mol) {
		boolean check=false;
		if(ConnectivityChecker.partitionIntoMolecules(mol).getAtomContainerCount() == 1) {
			check=true;
		}
		return check;
	}
	
	/**
	 * Molecule Generation Functions
	 */
	
	/**
	 * The function add a bond between two atoms or increase the bond order.
	 * @param mol atom container
	 * @param index atom index
	 * @param target target atom index
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static void bondAdder(IAtomContainer mol, int index, int target)throws CloneNotSupportedException, CDKException, IOException {
		IBond add = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		Order ord=null;
		if(add == null){ 					
			mol.addBond(index, target, IBond.Order.SINGLE);
		}
		else{
			ord = add.getOrder();
			if(ord == IBond.Order.SINGLE){
				mol.getBond(mol.getAtom(index), mol.getAtom(target)).setOrder(IBond.Order.DOUBLE);
			}
			else if(ord == IBond.Order.DOUBLE){
				mol.getBond(mol.getAtom(index), mol.getAtom(target)).setOrder(IBond.Order.TRIPLE);
			}
			//BondManipulator.increaseBondOrder(add); 
		}
	}
	
	/**
	 * Removing a bond from an atom container
	 * @param mol atom container
	 * @param index atom index
	 * @param target target atom index
	 */
	
	public static void removeBond(IAtomContainer mol, int index, int target) {
		IBond bond = mol.getBond(mol.getAtom(index), mol.getAtom(target)); 
		if(bond.getOrder()==Order.SINGLE) {
			mol.removeBond(bond);
		}else {
			BondManipulator.decreaseBondOrder(bond);
		}
	}
	
	/**
	 * For some cases, there was the bonds with order 4. To avoid that we need the function.
	 * @param mol IAtomContainer 
	 * @param index atom to saturate
	 * @param target atom to interact with
	 * @return
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static boolean fourth(IAtomContainer mol, int index, int target) throws CloneNotSupportedException, CDKException, IOException {
		boolean check=true;
		if(saturationChecker(mol,target)) {
			IBond bond=mol.getBond(mol.getAtom(index), mol.getAtom(target));
			if(bond!=null) {
				int ord=bond.getOrder().numeric();
				if(ord==3) {
					check=false;
				}
			}
		}
		return check;
	}
	
	/**
	 * Interacting atom with all the members of equivalence classes.
	 * @param mol atom container
	 * @param ec equivalence classes
	 * @param index atom index
	 * @param mols list of molecules
	 * @return List<IAtomContainer> list of atom containers
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static Set<IAtomContainer> atomExtensionAll(IAtomContainer mol, ListMultimap<String, Integer> ec, int index,List<Integer> indices,Set<IAtomContainer> mols) throws CloneNotSupportedException, CDKException, IOException { 	
		for(String key:ec.keySet()) {
			List<Integer> l=ec.get(key);
			for(Integer i:l) {
				if(index!=i && saturationChecker(mol,index) && saturationChecker(mol,i)){ 
					if(fourth(mol,index,i)) { // Just bond adder creates problem. even bonds with order 4.
						bondAdder(mol,index,i);
						IAtomContainer mol2=mol.clone();
						mols.add(mol2);
						removeBond(mol,index,i);
					}
				}
			}
		}
		return mols;
	}
	 
	//TODO: Currently we dont use CNI. For some test cases we miss some structures. 
	 
	/**
	 * CNI is the isomoprhism checking method explained in the article.
	 * @param ec equivalence classes.
	 * @param eClass an equivalence class
	 * @param mol atom container
	 * @return boolean true if the CNI conditions are satisfied.
	 */
		
	public static boolean CNI(ListMultimap<String, Integer> ec, List<Integer> eClass, IAtomContainer mol) {
		boolean check=true;
		for(Integer i:eClass) {
			for(String k:ec.keys()) {
				List<Integer> list= ec.get(k);
				for(Integer j: list) {
					if(i!=j) {
						if(mol.getBond(mol.getAtom(i), mol.getAtom(j))!=null) {
							check=false;
							break;
						}
					}
				}
			}
		}
		return check;
	}
			
	/**
	 * Equivalence classes based atom saturation function.
	 * @param mol IAtomContainer 
	 * @param index atom index to saturate
	 * @param satList the list of saturated molecules. - in which the atom is saturated.
	 * @param indices indices from a equivalence class.
	 * @return
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<IAtomContainer> atomSaturation(IAtomContainer mol,int index, List<IAtomContainer> satList,List<Integer> indices) throws CloneNotSupportedException, CDKException, IOException {
		/**
		 * If there is an interaction between the elements in the same class
		 * then the index, atom, would be already saturated. If we dont check,
		 * and add it to the list, this algorithm will return nothing. 
		 */
		if(!saturationChecker(mol,index)) { 
			satList.add(mol);
		}else {
			Set<IAtomContainer> mols= new HashSet<IAtomContainer>();
			ListMultimap<String, Integer> ec= equivalenceClass(mol);
			mols=atomExtensionAll(mol,ec,index,indices,mols);
			for(IAtomContainer ac:mols) {
				if(saturationChecker(ac,index)) {
					satList=atomSaturation(ac,index,satList,indices);
				}else if(!saturationChecker(ac,index)) {
					String inchi= inchiGeneration(ac);
					if(!atomSatInchiCheck.contains(inchi)) {
						atomSatInchiCheck.add(inchi);
						satList.add(ac);
					}
				}
			}
		}
	    return satList;
	}
	
	/**
	 * Equivalence classes based classSat function
	 * @param mol
	 * @param indices
	 * @param satList
	 * @return
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<IAtomContainer> classSat(IAtomContainer mol, List<Integer> indices, List<IAtomContainer> satList) throws CloneNotSupportedException, CDKException, IOException{
		if(indices.size()==0) {
			satList.add(mol);
		}else {
			int ind = (Integer)indices.get(0);
			List<Integer> newList= updateList(indices,ind);
			List<IAtomContainer> atomSatList = new ArrayList<IAtomContainer>();
			atomSatList=atomSaturation(mol,ind, atomSatList,newList);
			for(IAtomContainer ac: atomSatList) {
				String inchi=inchiGeneration(ac);				
				if(!classInchiCheck.contains(inchi)) {
					classInchiCheck.add(inchi);
					satList=classSat(ac,openSites(ac,newList),satList); //open sites need to be updated maybe.
				}
			}
		}
		return satList;
	}
	
	/**
	 * Equivalence classes based run function
	 * @param mol
	 * @param outFile
	 * @param list
	 * @return
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	
	public static List<IAtomContainer> run( IAtomContainer mol, SDFWriter outFile, List<IAtomContainer> list) throws CloneNotSupportedException, CDKException, IOException {
		saturation = new SaturationChecker();
		if(saturation.allSaturated(mol) && connectivityCheck(mol)) {
			String inchi=inchiGeneration(mol);
			if(!inchiCheck.contains(inchi)) {
				inchiCheck.add(inchi);
				list.add(mol);
				outFile.write(mol);
			}
		}else {
			ListMultimap<String, Integer> m=equivalenceClass(mol); 
			for(String k:m.keySet()) {
				List<Integer> l= m.get(k); 
				List<IAtomContainer> sat= new ArrayList<IAtomContainer>();
				sat=classSat(mol,l,sat);
				for(IAtomContainer a: sat) {
					list=run(a,outFile,list);
				}
			}
		}
		return list;
	}
	
	/**
	 * The main function to set the inputs and terminate the generation functions.
	 * @param molInfo molecular information
	 * @param fileDirectory Directory path for the output SDF file.
	 * @throws CloneNotSupportedException
	 * @throws CDKException
	 * @throws IOException
	 */
	 
	public static void EQGen(String molInfo, String fileDirectory) throws CloneNotSupportedException, CDKException, IOException {
		long startTime = System.nanoTime(); //Recording the duration time.
		SDFWriter outFile = new SDFWriter(new FileWriter(filedir+".sdf"));
		List<IAtomContainer> mols= new ArrayList<IAtomContainer>();
		IAtomContainer mol = build(molinfo); //The order of the molinfo for hydrogen dis. change the result.
		if(verbose) {
			System.out.println("Input molecule is built and its image is stored in the given directory.");
		}
        if(verbose) System.out.println("Start generating structures ...");
        run(mol,outFile,mols);
        long endTime = System.nanoTime()- startTime;
        double seconds = (double) endTime / 1000000000.0;
		DecimalFormat d = new DecimalFormat(".###");
        if(verbose) {
        	System.out.println("Number of generated structures:"+" "+mols.size());
        	System.out.println("Duration:"+" "+d.format(seconds)); //Format in second
        }
        outFile.close();	
	}
	
	private void parseArgs(String[] args) throws ParseException
	{
		Options options = setupOptions(args);	
		CommandLineParser parser = new DefaultParser();
		try {
			CommandLine cmd = parser.parse(options, args);
			Generator.molinfo = cmd.getOptionValue("molecularinfo");
			Generator.filedir = cmd.getOptionValue("filedir");
			Generator.fragments= cmd.getOptionValue("fragments");
			if (cmd.hasOption("verbose")) Generator.verbose = true;
		
		} catch (ParseException e) {
			HelpFormatter formatter = new HelpFormatter();
			formatter.setOptionComparator(null);
			String header = "\nGenerates structures for a given molecular information."
					+ " The input is the string of atom symbols with their number of implicit hydrogen."
					+ "For example 'C3C3C3' means three carbon atoms each of which has three implicit hydrogens."
					+ "Besides this molecular information, the directory is needed to be specified for the output"
					+ "file. \n\n";
			String footer = "\nPlease report issues at https://github.com/MehmetAzizYirik/EQGen";
			formatter.printHelp( "java -jar EQGen.jar", header, options, footer, true );
			throw new ParseException("Problem parsing command line");
		}
	}
	
	private Options setupOptions(String[] args)
	{
		Options options = new Options();
		Option molinfo = Option.builder("i")
			     .required(true)
			     .hasArg()
			     .longOpt("molecularinfo")
			     .desc("String of atoms with their implicit hydrogen information (required)")
			     .build();
		options.addOption(molinfo);
		Option verbose = Option.builder("v")
			     .required(false)
			     .longOpt("verbose")
			     .desc("Print messages about the duration time of the Gen")
			     .build();
		options.addOption(verbose);	
		Option filedir = Option.builder("d")
			     .required(true)
			     .hasArg()
			     .longOpt("filedir")
			     .desc("Creates and store the output sdf file in the directory (required)")
			     .build();
		options.addOption(filedir);
		Option fragments = Option.builder("f")
			     .required(false)
			     .hasArg()
			     .longOpt("fragments")
			     .desc("The list of substructures from experimental data")
			     .build();
		options.addOption(fragments);
		return options;
	}
	
	public static void main(String[] args) throws CloneNotSupportedException, CDKException, IOException  {		
		Generator gen = null;
		//O1CC1C1C1C1CO1 C6H6O2 Example formula
		//String[] args1 = {"-i","C1C1C1C1C1C1","-v","-d","C:\\Users\\mehme\\Desktop\\output\\ben" };
		try {
			gen = new Generator();
			gen.parseArgs(args);
			Generator.EQGen(Generator.molinfo, Generator.filedir);
		} catch (Exception e) {
			if (Generator.verbose) e.getCause(); 
		}
	}
}
