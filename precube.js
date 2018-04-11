function cv(arr){
	console.log('adding', arr)
	return new THREE.Vector3(arr[0], arr[1], arr[2]);
}

meshes = []
nhs = []

function animate() {
	requestAnimationFrame(animate);
	meshes.forEach( (mesh)=>{
		mesh.rotation.x += 0.006
		mesh.rotation.y += 0.06
		mesh.rotation.z += 0.00
	})
	nhs.forEach( (nh)=> nh.update() )
	window.renderer.render(window.scene, window.camera);
}

idx = 0

function addMeshFromQuads(q, color){
	console.log('quad time', q)
	var geometry = new THREE.Geometry()
	for (var i = 0; i < q.length - 3; i += 4){
		len = geometry.vertices.push(cv(q[i]), cv(q[i+1]), cv(q[i+2]), cv(q[i+3]));
		console.log('len', len)
		console.log(q[i], q[i+1], q[i+2])
		console.log(q[i], q[i+3], q[i+2])
		geometry.faces.push( new THREE.Face3(i,i+1,i+2, null, i==0 ? '#ff0000' : null) );
		geometry.faces.push( new THREE.Face3(i+2,i+3,i) );
	}
	geometry.computeBoundingSphere();
	geometry.computeBoundingBox();
	geometry.computeFaceNormals();
	geometry.colorsNeedUpdate = true;

	var material = new THREE.MeshBasicMaterial({color: color, transparent: true, opacity: 0.82, side: THREE.FrontSide, vertexColors: THREE.faceColors });
	mesh = new THREE.Mesh( geometry, material );
	meshes.push(mesh)
	nh = new THREE.FaceNormalsHelper( mesh, 80, 0xff8800, 6)
	nhs.push(nh)
	window.scene.add( mesh )
	//window.scene.add( nh )

	//window.renderer.render(window.scene, window.camera)
	++ idx
}

window.camera = new THREE.PerspectiveCamera( 70, window.innerWidth / window.innerHeight, 1, 10000 );
window.camera.position.z = 3400;
window.scene = new THREE.Scene();
window.renderer = new THREE.WebGLRenderer();
window.renderer.setPixelRatio( window.devicePixelRatio );
window.renderer.setSize( window.innerWidth, window.innerHeight );
document.body.appendChild( renderer.domElement );

animate()
