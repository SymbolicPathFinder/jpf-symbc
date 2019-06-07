package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InputOutput;
import jkind.lustre.NamedType;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractDiscoveryOn;

public class Contract {

    public final InOutManager inOutManager = new InOutManager();

    Contract(){
        inOutManager.discoverVars();
    }

    /**
     * This method is used to collect the input of a method, later for contract discovery or for lustre translation.
     * currently unused
     */
    public void collectInput(){
        if(!contractDiscoveryOn){
            System.out.println("collectInput is valid only when contractDiscovery is turned on");
            assert false;
        }
    }

}
