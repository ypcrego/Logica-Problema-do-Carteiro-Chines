package problema.carteiro.chines;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class Vertice {
    //@ spec_public
    private int n; // Identificador do vértice

    //@ spec_public
    private double d;
    //@ spec_public
    private double rot;
    public List<Integer> listaAdjascencia; // Lista de vértices do vértice

    //@ public invariant listaAdjascencia != null;
    //@ public invariant listaAdjascencia.size() >= 0;
    //@ public invariant n >= 0;

    //@ public normal_behavior
    //@ requires num >= 0;
    //@ ensures this.listaAdjascencia.size() == 0;
    //@ ensures this.listaAdjascencia != null;
    //@ ensures this.n >= 0;
    //@ ensures this.n == num;
    //@ ensures this != null;
    //@ pure
    public Vertice(int num){
        this.n = num;
        this.listaAdjascencia = new ArrayList<>();
    }
    //@ public normal_behavior
    //@ requires ver != null;
    //@ requires ver.listaAdjascencia != null;
    //@ requires ver.listaAdjascencia.size() >= 0;
    //@ requires ver.n >= 0;

    //@ ensures this.listaAdjascencia.size() >= 0;
    //@ ensures this.listaAdjascencia != null;
    //@ ensures this.n >= 0;
    //@ ensures this != null;
    //@ ensures this.n == ver.n;
    //@ ensures this.d == ver.d;
    //@ ensures this.rot == ver.rot;
    //@ ensures \forall int i; 0 <= i < this.listaAdjascencia.size(); this.listaAdjascencia.get(i) == ver.listaAdjascencia.get(i);

    //@ pure
    public Vertice(Vertice ver){
        this.n = ver.n;
        this.d = ver.d;
        this.rot = ver.rot;
        this.listaAdjascencia = new ArrayList<>(ver.listaAdjascencia);
    }

    //@ also public  normal_behavior
    //@ requires this == o;
    //@ ensures \result == true;
    //@ also public  normal_behavior
    //@ requires this != o && (o == null || getClass() != o.getClass());
    //@ ensures \result == false;
    //@ also public normal_behavior
    //@ requires this != o && !(o == null || getClass() != o.getClass());
    //@ ensures \result == (n == ((Vertice)o).n);
    //@ pure
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        return n == ((Vertice)o).n;
    }

    // @Override //comentado pois não é necessário para o funcionamento do código
    // public int hashCode() {
    //     return Objects.hash(n);
    // }

    //getters e setters

    //@ public normal_behavior
    //@ ensures \result == this.n;
    //@ pure
    public int getN(){
        return this.n;
    }

    //@ requires num >= 0;
    //@ ensures this.n == num;
    public void setN(int num){
        this.n = num;
    }

    //@ ensures \result == this.d;
    //@ pure
    public double getD(){
        return this.d;
    }

    public void setD(double d){
        this.d = d;
    }

    //@ ensures \result == this.rot;
    //@ pure
    public double getRot(){
        return this.rot;
    }

    public void setRot(double rot){
        this.rot = rot;
    }

    //@ ensures \result == this.listaAdjascencia.size();
    //@ pure
    public int getGrau(){
        return this.listaAdjascencia.size();
    }

    //@ ensures \result == this.listaAdjascencia;
    //@ pure
    public List<Integer> getListaAdjascencia(){
        return this.listaAdjascencia;
    }
}