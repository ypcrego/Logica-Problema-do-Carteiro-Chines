package problema.carteiro.chines;

import problema.carteiro.chines.Vertice;

// import org.checkerframework.checker.units.qual.A;

import java.util.*;

public class Grafo {
    //@ spec_public
    private int V = 0; // Número de vértices
    //@ spec_public
    private int L = 0; // Número de arestas
    //@ spec_public
    private List<Vertice> listaVertices = new ArrayList<Vertice>();

    //@ public invariant listaVertices != null;
    //@ public invariant listaVertices.size() >= 0;
    //@ public invariant \forall int i; 0 <= i < listaVertices.size(); listaVertices.get(i) != null;

    public Grafo() {
        listaVertices = new ArrayList<Vertice>();
    }

    /**
     * Função para adicionar um vértice no grafo.
     * 
     * @param v Vértice a ser adicionado
     */
    void addVertice(int v) {
        Vertice aux = new Vertice(v);
        if (!listaVertices.contains(aux))
            listaVertices.add(aux);
        this.V++;
    }

    /**
     * Função para adicionar uma aresta de 2 vértices.
     * 
     * @param v1 Vértice 1
     * @param v2 Vértice 2
     */

    void addAresta(int v1, int v2) {
        if (!verticeExiste(v1) || !verticeExiste(v2)){
            throw new IllegalArgumentException("O vértice v1 não existe");
        }

        Vertice auxv1 = new Vertice(v1);
        Vertice auxv2 = new Vertice(v2);
        int index1 = listaVertices.indexOf(auxv1);
        int index2 = listaVertices.indexOf(auxv2);

        listaVertices.get(index1).listaAdjascencia.add(v2);
        listaVertices.get(index2).listaAdjascencia.add(v1);
        this.L++;
    }

    Boolean verticeExiste(int n) {
        for (int i=0; i < listaVertices.size(); i++){
            if(listaVertices.get(i).getN() == n){
                return true;
            }
        }
        return false;
    }

    /**
     * Função para remover uma aresta de 2 vértices.
     * 
     * @param v1 Vértice 1
     * @param v2 Vértice 2
     */
    void remAresta(int v1, int v2) {
        Vertice auxv1 = new Vertice(v1);
        Vertice auxv2 = new Vertice(v2);
        try {
            listaVertices.get(listaVertices.indexOf(auxv1)).listaAdjascencia.remove(new Integer(v2));
            listaVertices.get(listaVertices.indexOf(auxv2)).listaAdjascencia.remove(new Integer(v1));
        } catch (NullPointerException e) {
            e.printStackTrace();
            System.out.println("O vértice não existe");
        }
        this.L--;
    }

    //@ ensures \forall int i; 0 <= i < this.listaVertices.size(); this.listaVertices.get(i) != null;
    public void printGrafo() {
        //@ maintaining 0 <= i <= this.listaVertices.size();
        //@ loop_writes i;
        //@ decreases this.listaVertices.size() - i;
        for (int i=0; i < this.listaVertices.size(); i++) {
            System.out.print(this.listaVertices.get(i).getN() + ": ");
            //@ maintaining 0 <= j <= this.listaVertices.get(i).listaAdjascencia.size();
            //@ loop_writes j;
            //@ decreases this.listaVertices.get(i).listaAdjascencia.size() - j;
            for (int j=0; j < this.listaVertices.get(i).listaAdjascencia.size(); j++) {
                System.out.print(this.listaVertices.get(i).listaAdjascencia.get(j) + " ");
            }
            System.out.println();
        }
    }

    //@ ensures \forall int i; 0 <= i < this.listaVertices.size(); this.listaVertices.get(i) != null;
    public void printVertices() {
        //@ maintaining 0 <= i <= this.listaVertices.size();
        //@ loop_writes i;
        //@ decreases this.listaVertices.size() - i;
        for (int i=0; i < this.listaVertices.size(); i++) {
            System.out.print("(n: " + listaVertices.get(i).getN() + " d: " + listaVertices.get(i).getD() + " rot: " + listaVertices.get(i).getRot() + ") \n");
        }
    }

    // Getters e Setters

    //@ ensures \result == this.V;
    //@ pure
    public int getV() {
        return V;
    }

    //@ requires v >= 0;
    //@ assigns this.V;
    //@ ensures this.V == v;
    public void setV(int v) {
        V = v;
    }

    //@ ensures \result == this.L;
    //@ pure
    public int getL() {
        return L;
    }

    //@ requires l >= 0;
    //@ assigns this.L;
    //@ ensures this.L == l;
    public void setL(int l) {
        L = l;
    }

    //@ ensures \result == this.listaVertices;
    //@ pure
    public List<Vertice> getListaVertices() {
        return listaVertices;
    }

    //@ normal_behavior
    //@     requires lista != null;
    //@     requires lista.size() >= 0;
    //@     requires \forall int i; 0 <= i <= lista.size(); lista.get(i) != null;
    //@     assigns this.listaVertices;
    //@     ensures \forall int i; 0 <= i < this.listaVertices.size(); this.listaVertices.get(i) == lista.get(i);
    //@     ensures \forall int i; 0 <= i < this.listaVertices.size(); this.listaVertices.get(i) != null;
    //@ exceptional_behavior
    //@     requires lista == null;
    //@     assigns \nothing;
    //@     signals_only IllegalArgumentException;
    public void setListaVertices(List<Vertice> lista) {
        if (lista == null) {
            throw new IllegalArgumentException("Lista não pode ser nula!");
        }

        //@ maintaining 0 <= i <= lista.size();
        //@ loop_writes i;
        //@ decreases lista.size() - i;
        for (int i=0; i< lista.size(); i++) {
            if (lista.get(i) == null) {
                throw new IllegalArgumentException("A lista contém elementos nulos!");
            }
        }

        this.listaVertices = new ArrayList<Vertice>();
        //@ maintaining 0 <= i <= lista.size();
        //@ loop_writes i;
        //@ decreases lista.size() - i;
        for (int i = 0; i < lista.size(); i++) {
            Vertice v = lista.get(i);
            this.listaVertices.add(v);
        }
    }
}